#!/usr/bin/env python
################################################################################
#
# snap.py
#
# bloatbear@googlemail.com
#
# Script that makes rsync snapshots of lvm volumes and backup rotation
#
################################################################################


import sys,os,datetime,tempfile,shutil,socket
import string,random
from subprocess import *
from optparse import OptionParser
from cStringIO import StringIO
import MySQLdb
import tarfile
import logging
import logging.handlers
from ftplib import FTP
import netrc
import time

def strfDate(date=datetime.datetime.now()):
    return "%d-%02d-%02d-%02d:%02d:%02d" %(date.year,date.month,date.day,date.hour,date.minute,date.second)

def datefStr(dateStr):
    return datetime.datetime.strptime(dateStr,"%Y-%m-%d-%H:%M:%S")

def execute(lCall,logger):
    try:
        proc = Popen(lCall, stdout=PIPE, stderr=PIPE, stdin=PIPE)
        stdout, stderr = proc.communicate()
        retcode = proc.returncode
        for line in stdout.split("\n"): 
            if len(line):
                if not line.startswith(lCall[0]): line = "%s: %s"%(lCall[0],line)
                logger.debug(line)
        for line in stderr.split("\n"): 
            if len(line):
                if not line.startswith(lCall[0]): line = "%s: %s"%(lCall[0],line)
                logger.debug(line)
        if retcode > 0: logger.error("%s returned %s"%(lCall[0],retcode))
        elif retcode < 0: logger.error("%s was terminated by signal %s"%(lCall[0],-retcode))
        else: logger.debug("%s terminated successfull with %s"%(lCall[0],-retcode))
    except OSError, e: logger.exception("Execution of %s failed: %s" %(lCall[0],e))
    return retcode

class Log:
    __LOG_FILENAME = '/var/log/backup.log'
    __SMTP_HOST = 'localhost'
    __FROM = 'snap.py@' + socket.gethostname()
    __RCPT = 'root'
    __SUBJECT = socket.gethostname() + ' backup problems.'

    def __init__(self,name,verbose):
        self.logger = logging.getLogger(name)
        self.logger.setLevel(logging.DEBUG) 
        # create file handler which logs even debug messages 
        self.__fh = logging.FileHandler(self.__LOG_FILENAME)
        self.__fh.setLevel(logging.INFO) 

        # create formatter and add it to the handlers 
        self.__formatter = logging.Formatter("%(asctime)s %(name)s [%(levelname)s] - %(message)s","%b %d %H:%M:%S") 
        self.__fh.setFormatter(self.__formatter)
        self.logger.addHandler(self.__fh)
        if verbose:
            # create console handler with a higher log level 
            self.__ch = logging.StreamHandler()
            self.__ch.setFormatter(self.__formatter) 
            self.__ch.setLevel(logging.DEBUG) 
            self.logger.addHandler(self.__ch)
        else:
            # create email handler
            self.__mh = logging.handlers.SMTPHandler(self.__SMTP_HOST,self.__FROM, self.__RCPT, self.__SUBJECT)
            self.__mh.setFormatter(self.__formatter) 
            self.__mh.setLevel(logging.WARNING) 
            self.logger.addHandler(self.__mh)

    def write(self, msg, level=logging.INFO):
        self.logger.log(level, msg)

    def flush(self):
        for handler in self.logger.handlers:
            handler.flush()

class Fs:
    """ """
    def __init__(self,lv,mp='',size=0, isTmp=False, logger=logging.getLogger()):
        self.logger = logger
        self.__lv = str(lv)
        self.__devStr = os.path.join("/dev",self.__lv)
        self.__mpTmp = False
        self.__mp = os.path.join("/tmp",self.__lv.split("/")[1])
        if len(mp): self.__mp = str(mp)
        self.__lvmSnapSize = size
        self.__isTmp = isTmp
        self.__isMounted = os.path.ismount(self.__mp)

    def __del__(self):
        if self.__mpTmp:
            if self.__isMounted: self.umount()
            os.rmdir(self.__mp)
        if self.__isTmp:
            if self.__isMounted: self.umount()
            self.removeLvmSnapshot()

    def mount(self):
        if os.path.exists(self.__mp):
            if os.path.ismount(self.__mp):
                self.logger.warning("Another file system is already mounted on %s. Unmounting it."%self.__mp)
                self.umount()
        else:
            os.mkdir(self.__mp)
            self.__mpTmp = True
        self.logger.debug("mounting " + self.__devStr + " on " + self.__mp)
        lCall = ["mount",self.__devStr,self.__mp]
        if 0 == execute(lCall,self.logger): self.__isMounted = True

    def umount(self):
      nTries = 0;
      maxTries = 60;
      self.sync()
      self.logger.debug("unmounting " + self.__devStr + " from " + self.__mp)
      lCall = ["umount",self.__mp]
      while execute(lCall,self.logger): 
	nTries += 1
	if nTries >= maxTries: 
	  lCall = ["umount","-l",self.__mp]
	  execute(lCall,self.logger)
	  self.logger.warning("Reached max number of %d umount tries of %s. Doing lazy umount." %(nTries,self.__mp))
	  break
	time.sleep(1)
      else: self.logger.debug("Took %d tries to umount %s." %(nTries,self.__mp))
      self.__isMounted = False

    def isMounted(self): return self.__isMounted
    def lv(self): return self.__lv
    def mp(self): return self.__mp

    def takeLvmSnapshot(self,name=''):
        if not len(name): name = "__snapshot_"+self.__lv.split("/")[1]
        dev = os.path.join("/dev",self.__lv.split("/")[0],name)
        if os.path.exists(dev):
            self.logger.warning("LVM snapshot %s already exists. Removing it."%dev)
            fs = Fs(self.__lv.split("/")[0]+"/"+str(name),isTmp=True,logger=self.logger)
            del fs
        lCall = ["/sbin/lvcreate","-s","-L",str(self.__lvmSnapSize)+"G","-n",str(name),self.__devStr]
        execute(lCall,self.logger)
        return Fs(lv=self.__lv.split("/")[0]+"/"+str(name), size=self.__lvmSnapSize, isTmp = True, logger=self.logger)

    def removeLvmSnapshot(self,dev=''):
        if not len(dev): dev = self.__devStr
        lCall = ["/sbin/lvremove","-f",dev]
        execute(lCall,self.logger)

    def sync(self):
      lCall = ["sync"]
      execute(lCall,self.logger)

class Snapshot:
    """ """
    
    __Intervals = ["frequent","hourly","daily","weekly","monthly","yearly"]
    __Modes = dict(hourly=1/24.,daily=1.,weekly=7.,monthly=28.,yearly=365.)

    def __init__(self,name,backupRoot,compress,logger):
        self.__name = name
        self.__backupRoot = backupRoot
        self.__compress = compress
        self.logger = logger
        self.__cwd = os.getcwd()

        self.__snapRoot = os.path.join(self.__backupRoot,self.__name)
        if not os.path.isdir(self.__snapRoot):
            os.makedirs(self.__snapRoot)
            self.logger.info("Backup dir %s created" %self.__snapRoot)
        
        self.__snapshots=dict([(key,[]) for key in self.__Intervals])
    
    def scanSnapRoot(self):
        for f in os.listdir(self.__snapRoot):
            if (os.path.isdir(os.path.join(self.__snapRoot,f))) or (tarfile.is_tarfile(os.path.join(self.__snapRoot,f))):
                if(len(f.split("@"))==2):
                    (mode,dateStr) = f.split("@")
                    if mode in self.__Intervals:
                        self.__snapshots[mode].append(datefStr(dateStr.split(".tar.gz")[0]))
                        self.__snapshots[mode].sort()
                else:
                    self.logger.warning("Additional directory %s found in %s. Please clean up." %(f,dir))

    def newSnap(self,fs):
        now = datetime.datetime.now()
        snap = os.path.join(self.__snapRoot,"frequent@"+strfDate(now))
        recentSnap = ""
        # is there already another frequent snapshot to link against
        if len(self.__snapshots["frequent"]):
            recentSnap = "frequent@"+strfDate(self.__snapshots["frequent"][-1])
        if not fs.isMounted(): fs.mount()

        if self.__compress:
            snap += ".tar.gz"
            os.chdir(fs.mp())
            tar = tarfile.open(snap,"w:gz")
            tar.add(".")
            tar.close()
            os.chdir(self.__cwd)
        else:
            lCall = ["rsync","-rlptgo","--delete","--link-dest=../"+recentSnap,fs.mp()+"/",snap+"/"]
            execute(lCall,self.logger)
        
        self.logger.info("%s: new snapshot %s"%(self.__name,os.path.split(snap)[1]))

        # append to frequent snapshots
        self.__snapshots["frequent"].append(now)

    def rotateSnaps(self):
        for i in range(len(self.__Intervals)-1):
            cur = self.__Intervals[i]
            nex = self.__Intervals[i+1]
            # timedelta of next interval plus 1% uncertainty
            delta = datetime.timedelta(days=(self.__Modes[nex]*0.99))

            # no current or next snapshots ... maybe first run
            if not (len(self.__snapshots[cur]) or len(self.__snapshots[nex])): continue
            # only current snapshot available
            elif len(self.__snapshots[cur]) and not len(self.__snapshots[nex]):
                # oldest current snapshot is ready for next level
                if (self.__snapshots[cur][-1]-self.__snapshots[cur][0]>=delta): self.__mvSnap(cur,nex)
            # current and next snapshots available, regular behavior
            elif len(self.__snapshots[cur]) and len(self.__snapshots[nex]):
                # oldest current snapshot is ready for next level
                if (self.__snapshots[cur][0]-self.__snapshots[nex][-1]>=delta): self.__mvSnap(cur,nex)
                # oldest current snapshot not old enough for rotation, simply deleting it
                elif (self.__snapshots[cur][-1]-self.__snapshots[cur][0]>=delta): self.__popSnap(cur)

    def __mvSnap(self,srcMode,dstMode):
        date = self.__snapshots[srcMode].pop(0)
        self.__snapshots[dstMode].append(date)
        src = os.path.join(self.__snapRoot,srcMode+"@"+strfDate(date))
        dst = os.path.join(self.__snapRoot,dstMode+"@"+strfDate(date))
        if os.path.exists(src+".tar.gz"):
            src += ".tar.gz"
            dst += ".tar.gz"
        shutil.move(src,dst)
        self.logger.info("%s: rotated snapshot %s to %s" %(self.__name,os.path.split(src)[1],os.path.split(dst)[1]))
    def __popSnap(self,mode):
        date = self.__snapshots[mode].pop(0)
        path = os.path.join(self.__snapRoot,mode+"@"+strfDate(date))
        if os.path.isdir(path): shutil.rmtree(path)
        elif tarfile.is_tarfile(path+".tar.gz"):
            path += ".tar.gz"
            os.unlink(path)
        self.logger.info("%s: removed snapshot %s" %(self.__name,os.path.split(path)[1]))


class MyFTP (FTP, netrc.netrc):
    """ """
    def __init__(self,host,path,logger=logging.getLogger("MyFTP")):
        self.logger = logger
        FTP.__init__(self)
        self.__isConnected = False
        try:
            self.connect(host)
        except Exception as inst: 
            self.logger.error("FTP: %s"%inst)
        else:
            netrc.netrc.__init__(self)
            auth = self.authenticators(host)
            try:
                self.login(auth[0],auth[2])
            except Exception as inst: 
                self.logger.error("FTP: %s"%inst)
            else:
                try:
                    self.cwd(path)
                except Exception as inst:
                    self.logger.error("FTP: %s"%inst)
                else:
                    self.__isConnected = True

    def sendFile(self,path): 
                try:
                    self.storbinary("STOR %s"%os.path.split(path)[1],open(path,"rb"))
                except Exception as inst:
                    self.logger.error("FTP: %s"%inst)

    def isConnected(self): return self.__isConnected

    def __del__(self):
        if self.__isConnected: self.quit()

class Lock:
    """ """

    __LockRoot = "/var/lock/backup"

    def __init__(self,lv,logger):
	(self.__vg,self.__lv) = lv.split("/")
	self.logger = logger
	self.__locked = False
	self.__lockDir = os.path.join(self.__LockRoot,self.__vg)
	self.__lockFile = os.path.join(self.__LockRoot,self.__vg,self.__lv)
        if not os.path.isdir(self.__lockDir):
            os.makedirs(self.__lockDir)
            self.logger.info("Lock dir %s created" %self.__lockDir)

    def lock (self):
	if os.path.exists(self.__lockFile):
	    self.logger.warning("Lock file %s already exists." %self.__lockFile)
	    return -1
	open(self.__lockFile, 'w').close() 
	if not os.path.exists(self.__lockFile):
	    self.logger.error("Could not create lock file %s." %self.__lockFile)
	    return -2
	self.logger.debug("Lock file %s created." %self.__lockFile)
	self.__locked = True
	return 0

    def unlock (self):
	if not os.path.exists(self.__lockFile):
	    self.logger.warning("Lock file %s does not exists." %self.__lockFile)
            return -1
	os.unlink(self.__lockFile)
        if os.path.exists(self.__lockFile):
            self.logger.error("Error removing lock file %s." %self.__lockFile)
            return -2
        self.logger.debug("Lock file %s removed." %self.__lockFile)
	self.__locked = False
        return 0

    def locked (self): return self.__locked
	    

class RCSnapshot (Log):
    """ """
    def __init__(self,optStr):
        self.__parseOpts(optStr)
        Log.__init__(self,"Snapshot",verbose=self.__verbose)
        
    def run(self):
        self.__snapshots = {}
        self.__srcFs = {}
        self.__lvmSnapshots = {}
	self.__locks = {}

	for lv in self.__lvList:
            self.__locks[lv] = Lock(lv,self.logger)
	    self.__locks[lv].lock()
	    if not self.__locks[lv].locked():
	       self.logger.error("Could not lock backup on %s. Skipping." %lv)
	       continue
            
            compress = lv in self.__compress or self.__compress[0] == "all";
                
            self.__snapshots[lv] = Snapshot(name=lv,backupRoot=self.__backupRoot,compress=compress,logger=self.logger)
            self.__srcFs[lv] = Fs(lv,size=self.__lvmSnapSize, isTmp=False, logger=self.logger)

        for snapshot in self.__snapshots.values(): snapshot.scanSnapRoot()

        if self.__withReadlock: self.__lock()

        for lv in self.__srcFs.keys(): 
	    if not self.__locks[lv].locked(): continue

	    self.__lvmSnapshots[lv] = self.__srcFs[lv].takeLvmSnapshot()


        if self.__withReadlock: self.__unlock()

        for lv in self.__snapshots.keys():
            self.__snapshots[lv].newSnap(self.__lvmSnapshots[lv])
	    del self.__lvmSnapshots[lv]
            self.__snapshots[lv].rotateSnaps()
	    self.__locks[lv].unlock()

    def __parseOpts(self,optStr):
        self.__parser = OptionParser("usage: %prog [options] snapshot")
        self.__parser.add_option("-b", "--broot", dest="backupRoot", default="/backup", metavar="DIR",
                          help="Backup root path [default: %default]")
        self.__parser.add_option("-c", dest="compress", default="none", metavar="none|all|VG/LV[,VG/LV]",
                               help="Compress snapshots (Disables the use of hard links.). [default: %default]")
        self.__parser.add_option("-l", "--lv", dest="lv", help="Comma seperated list of LVs.", metavar="VG/LV")
        self.__parser.add_option("-s", "--size", dest="size", default=2,
                               help="lvm snapshot size in GByte [default: %default]")
        self.__parser.add_option("-r", "--readlock", action="store_true", dest="readlock", default=False,
                               help="\"FLUSH TABLES AND READ LOCK\" local mysql server before snapshoting [default: %default]")
        self.__parser.add_option("-v", "--verbose", action="store_true", dest="verbose", default=False,
                               help="make noise [default: %default]")
        (options,args) = self.__parser.parse_args(optStr)

        if not options.lv: self.__parser.error("No or empty Logical Volume path provided. Use \"-l\" option.")
        if not os.path.isdir(options.backupRoot): self.__parser.error("Backup directory \"%s\" does not exist."%options.backupRoot)

        self.__verbose = options.verbose
        self.__withReadlock = options.readlock
        self.__lvmSnapSize = options.size
        #self.__compress = options.compress
        self.__compress = options.compress.split(",")
        #(self.__vg,self.__lv) = options.lv.split("/")
        self.__lvList = options.lv.split(",")
        self.__backupRoot = options.backupRoot

    def __lock(self):
        self.__dbh = MySQLdb.connect(read_default_file="/etc/mysql/my.cnf")
        self.__dbh.query("flush tables with read lock;")
        self.logger.debug("Local MySql databases locked.")

    def __unlock(self):
        self.__dbh.query("show master status;")
        r = self.__dbh.store_result()
        self.__binlog = r.fetch_row()
        self.__dbh.close()
        self.logger.debug("Local MySql databases UNlocked. Binlog: %s" %self.__binlog)
        self.logger.info("%s: MySQL binlog file[pos]: %s[%s]" %(socket.gethostname(),self.__binlog[0][0],self.__binlog[0][1]))

class RCList:
    """ """
    def __init__(self,optStr):
        self.__parseOpts(optStr)
        self.__snapshotsList = {}
        
    def run(self):
        if 0==len(self.__lvList[0]): self.overallStats()

    def stats(self,lv):
        pass

    def overallStats(self):
        for vg in os.listdir(self.__backupRoot):
            if os.path.isdir(os.path.join(self.__backupRoot,vg)):
                for lv in os.listdir(os.path.join(self.__backupRoot,vg)):
                    print vg,lv

    def __parseOpts(self,optStr):
        self.__parser = OptionParser("usage: %prog [options] list")
        self.__parser.add_option("-b", "--broot", dest="backupRoot", default="/backup", metavar="DIR",
                          help="Backup root path [default: %default]")
        self.__parser.add_option("-l", "--lv", dest="lv", default="", help="Comma seperated list of LVs.", metavar="VG/LV")

        self.__parser.add_option("-v", "--verbose", action="store_true", dest="verbose", default=False,
                               help="make noise [default: %default]")
        (options,args) = self.__parser.parse_args(optStr)

        if not os.path.isdir(options.backupRoot): self.__parser.error("Backup directory \"%s\" does not exist."%options.backupRoot)

        self.__verbose = options.verbose
        self.__lvList = options.lv.split(",")
        self.__backupRoot = options.backupRoot

class RCSend (Log):
    """ """
    def __init__(self,optStr):
        self.__parseOpts(optStr)
        Log.__init__(self,"Send",verbose=self.__verbose)
        self.__cwd = os.getcwd()

    def __del__(self):
        pass
        
    def run(self):
        self.__oFs = Fs(self.__lv,size=30, isTmp=False, logger=self.logger)
        self.__sFs = self.__oFs.takeLvmSnapshot()
        self.__sFs.mount()
        
        for vg in os.listdir(self.__sFs.mp()):
            if vg == "lost+found": continue
            for lv in os.listdir(os.path.join(self.__sFs.mp(),vg)):
                if os.path.isdir(os.path.join(self.__sFs.mp(),vg,lv)):
                    file = os.path.join(self.__path,"%s_%s.tar.gz" %(vg,lv))
                    src = os.path.join(self.__sFs.mp(),vg,lv)
                    #tar = Popen(["tar","-C",src,"-czf","-","."], stdout=PIPE, stderr=PIPE)
                    tar = Popen(["tar","-C",src,"-cf","-","."], stdout=PIPE, stderr=PIPE)
                    gzip = Popen(["gzip"],stdin=tar.stdout,stdout=PIPE,stderr=PIPE)
                    curl = Popen(["curl","--limit-rate","4m","-nsS","ftp://"+self.__host+file,"-T","-"], stdin=gzip.stdout, stdout=PIPE, stderr=PIPE)
                    output = curl.communicate()
                    if len(output[0]): self.logger.info("FTP/TAR: %s"%output[0])
                    if len(output[1]): self.logger.error("FTP/TAR: %s"%output[1])
                    else: self.logger.info("FTP/TAR: Uploaded %s to ftp://%s%s"%(file,self.__host,self.__path))

    def __parseOpts(self,optStr):
        self.__parser = OptionParser("usage: %prog [options] send")
        self.__parser.add_option("--host", dest="host", help="Hostname of remote ftp server.")
        self.__parser.add_option("-p", "--path", dest="path", default="/", metavar="DIR",
                                 help="Backup root on remote ftp server [default: %default]")
        self.__parser.add_option("-c", "--compress", action="store_true", dest="compress", default=False,
                               help="Compress backups. [default: %default]")
        self.__parser.add_option("-l", "--lv", dest="lv", default="raid/backup", metavar="VG/LV"
                                 , help="Backup LV [default: %default]")
        self.__parser.add_option("-v", "--verbose", action="store_true", dest="verbose", default=False,
                               help="make noise [default: %default]")
        (options,args) = self.__parser.parse_args(optStr)

        if not options.lv: self.__parser.error("No or empty Logical Volume path provided. Use \"-l\" option.")

        self.__host = options.host
        self.__verbose = options.verbose
        self.__compress = options.compress
        self.__path = options.path
        self.__lv = options.lv

def main():
        if not len(sys.argv) > 1:
                print "No command line options provided."
                usage()
        
        if not sys.argv[1] in ["-h", "--help", "snapshot", "list", "send"]:
                print str(sys.argv[1]) + " is not a recognized command."
                usage()

        if sys.argv[1] == "snapshot":
            RCSnapshot(sys.argv[2:]).run()
                
        elif sys.argv[1] == "list":
            RCList(sys.argv[2:]).run()

        elif sys.argv[1] == "send":
            RCSend(sys.argv[2:]).run()

        elif (sys.argv[1] == "-h" or sys.argv[1] == "--help"):
            usage()
                
        sys.exit(0)

def usage():
    print "snap.py - LVM based backup tool"
    print "Syntax: snap.py command [options] <name>"
    print
    print "Valid commands are:"
    print "  snapshot                         Create snaphshot."
    print "  list                             List snaphosts."
    print "  send                             Send TARed snapshots"
    print
    print "Use \'snap.py command -h\' for information on individual commands." 
    sys.exit(0)

if __name__ == "__main__":
    main()

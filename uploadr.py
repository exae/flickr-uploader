#!/usr/bin/env python

"""

	flickr-uploader designed for Synology Devices
	Upload a directory of media to Flickr to use as a backup to your local storage.

	Features:

	-Uploads both images and movies (JPG, PNG, GIF, AVI, MOV, 3GP files)
	-Stores image information locally using a simple SQLite database
	-Automatically creates "Sets" based on the folder name the media is in
	-Ignores ".picasabackup" directory
	-Automatically removes images from Flickr when they are removed from your local hard drive

	Requirements:

	-Python 2.7+
	-File write access (for the token and local database)
	-Flickr API key (free)

	Setup:

	Go to http://www.flickr.com/services/apps/create/apply and apply for an API key Edit the following variables in the uploadr.ini

	FILES_DIR = "files/"
	FLICKR = { "api_key" : "", "secret" : "", "title" : "", "description" : "", "tags" : "auto-upload", "is_public" : "0", "is_friend" : "0", "is_family" : "1" }
	SLEEP_TIME = 1 * 60
	DRIP_TIME = 1 * 60
	DB_PATH = os.path.join(FILES_DIR, "fickerdb")
	Place the file uploadr.py in any directory and run:

	$ ./uploadr.py

	It will crawl through all the files from the FILES_DIR directory and begin the upload process.

	Upload files placed within a directory to your Flickr account.

   Inspired by:
		http://micampe.it/things/flickruploadr
		https://github.com/joelmx/flickrUploadr/blob/master/python3/uploadr.py

   Usage:

   cron entry (runs at the top of every hour )
   0  *  *  *  * /full/path/to/uploadr.py > /dev/null 2>&1

   This code has been updated to use the new Auth API from flickr.

   You may use this code however you see fit in any form whatsoever.

   Changes:

	2015-03-15 exae 
	+ SETS: creating sets from full path of the file
	+ SETS: creating the set since the first picture is loaded
	+ SETS: flickr folder and personal folder no interaction
	+ TAG: tag from folder name
	+ LOG: logging to file
	+ STATS: calc kbps for each file
	+ STATS: time process
	+ DB: only one connection
	+ SETTINGS : Limit upload to max number files and max time
	+ MAIL: mail repport when done
	
"""

import sys

if sys.version_info < (2, 7):
	sys.stderr.write("This script requires Python 2.7 or newer.\n")
	sys.stderr.write("Current version: " + sys.version + "\n")
	sys.stderr.flush()
	sys.exit(1)

import argparse
import mimetools
import mimetypes
import os
import time
import urllib
import urllib2
import webbrowser
import sqlite3 as lite
import json
from xml.dom.minidom import parse
import hashlib
import fcntl
import errno
import subprocess
import re
import logging
import mailit

# #
# # Read Config from config.ini file
# #

import ConfigParser
config = ConfigParser.ConfigParser()
config.read(os.path.join(os.path.dirname(sys.argv[0]), "uploadr.ini"))
FILES_DIR = eval(config.get('Config', 'FILES_DIR'))
ROOT_DIR = eval(config.get('Config', 'ROOT_DIR'))
FLICKR = eval(config.get('Config', 'FLICKR'))                        # structure flickr
SLEEP_TIME = eval(config.get('Config', 'SLEEP_TIME'))
DRIP_TIME = eval(config.get('Config', 'DRIP_TIME'))
DB_PATH = eval(config.get('Config', 'DB_PATH'))
LOCK_PATH = eval(config.get('Config', 'LOCK_PATH'))
TOKEN_PATH = eval(config.get('Config', 'TOKEN_PATH'))
LOG_PATH = eval(config.get('Config', 'LOG_PATH'))
EXCLUDED_FOLDERS = eval(config.get('Config', 'EXCLUDED_FOLDERS'))
IGNORED_REGEX = [re.compile(regex) for regex in eval(config.get('Config', 'IGNORED_REGEX'))]
ALLOWED_EXT = eval(config.get('Config', 'ALLOWED_EXT'))
RAW_EXT = eval(config.get('Config', 'RAW_EXT'))
FILE_MAX_SIZE = eval(config.get('Config', 'FILE_MAX_SIZE'))
MANAGE_CHANGES = eval(config.get('Config','MANAGE_CHANGES'))
RAW_TOOL_PATH = eval(config.get('Config', 'RAW_TOOL_PATH'))
CONVERT_RAW_FILES = eval(config.get('Config', 'CONVERT_RAW_FILES'))
MAX_FILES = eval(config.get('Config', 'MAX_FILES'))
MAX_MINUTES = eval(config.get('Config', 'MAX_MINUTES'))
SMTP_USER = eval(config.get('Config', 'SMTP_USER'))
SMTP_PASS = eval(config.get('Config', 'SMTP_PASS'))

logname = LOG_PATH + time.strftime("%d%m%y_%H%M.log",time.localtime() )
logging.basicConfig(filename=logname, level=logging.DEBUG, mode='w', format='%(asctime)s [%(levelname)s] %(message)s', datefmt="%Y-%m-%d %H:%M:%S")

def kbpsToStr( size, ms ):
	kbps = "%.2f kB/s" % ( size / ms / 1000.0 )	
	return kbps

# secondes vers chaine
def sectostr(tps):
	seconde = tps
	jour = 0
	heure = 0
	minute = 0
	if(seconde>=60):
		minute= seconde/60
		seconde= seconde%60
		if(minute>=60):
			heure=minute/60
			minute=minute%60
			if(heure>=24):
				jour=heure/24
				heure=heure%24
	if jour > 0:
		return '%d j %d h' % ( jour, heure )
	elif heure > 0:
		return '%d h %d min' % ( heure, minute )
	elif minute > 0:
		return '%d min %d sec' % ( minute, seconde )
	else:
		return '%d sec' % ( seconde )

# #
# #  You shouldn't need to modify anything below here
# #

class APIConstants:
	""" APIConstants class
	"""

	base = "https://api.flickr.com/services/"
	rest = base + "rest/"
	auth = base + "auth/"
	upload = base + "upload/"
	replace = base + "replace/"

	def __init__(self):
		""" Constructor
		"""
		pass
		
api = APIConstants()

class Uploadr:
	""" Uploadr class
	"""

	token = None
	perms = ""
	cnx   = None
	qry   = None
		
	def __init__(self):
		self.token = self.getCachedToken()
		# connexion a la base
		self.setupDB()
		self.lastset = ''
		self.lastsetid = ''
		self.tps       = time.time()
		self.starttime = time.time()		
		self.count     = 0		# Nombre total		
		self.newcount  = 0		# Nombre de fichier nouveau
		self.nbrficadd = 0      # Nb de fichiers uploads
		self.nbrficrep = 0		
		self.nbrficdel = 0
		self.nbrsetadd = 0
		self.nbrsetdel = 0
		self.nbrtag    = 0
		self.step      = 0
		self.uploaded = []		# les fichiers uploades
		
	# Destructeur
	def __del__(self):
		self.cnx.close()		
		
	# Base de donnees
	def setupDB(self):
		logging.debug("Setting up the database: " + DB_PATH)
		try:
			self.cnx = lite.connect(DB_PATH)
			self.cnx.text_factory = str		
			self.qry = self.cnx.cursor()
			self.qry.execute('create table if not exists files (files_id int, path text, set_id int, md5 text, tagged int)')
			self.qry.execute('create table if not exists sets (set_id int, name text, primary_photo_id INTEGER)')
			self.cnx.commit()
		except lite.Error, e:
			logging.error("Error: %s" % e.args[0])
			if self.cnx != None:
				self.cnx.close()
			sys.exit(1)
		finally:
			logging.debug("Completed database setup")
			
	def signCall(self, data):
		"""
		Signs args via md5 per http://www.flickr.com/services/api/auth.spec.html (Section 8)
		"""
		keys = data.keys()
		keys.sort()
		foo = ""
		for a in keys:
			foo += (a + data[a])

		f = FLICKR[ "secret" ] + "api_key" + FLICKR[ "api_key" ] + foo
		# f = "api_key" + FLICKR[ "api_key" ] + foo

		return hashlib.md5(f).hexdigest()

	def urlGen(self , base, data, sig):
		""" urlGen
		"""
		data['api_key'] = FLICKR[ "api_key" ]
		data['api_sig'] = sig
		encoded_url = base + "?" + urllib.urlencode(data)
		return encoded_url


	def authenticate(self):
		""" Authenticate user so we can upload files
		"""

		logging.info("Getting new token")
		self.getFrob()
		self.getAuthKey()
		self.getToken()
		self.cacheToken()

	def getFrob(self):
		"""
		flickr.auth.getFrob

		Returns a frob to be used during authentication. This method call must be
		signed.

		This method does not require authentication.
		Arguments

		"api_key" (Required)
		Your API application key. See here for more details.
		"""

		d = {
			"method"		  : "flickr.auth.getFrob",
			"format"		  : "json",
			"nojsoncallback"	: "1"
			}
		sig = self.signCall(d)
		url = self.urlGen(api.rest, d, sig)
		try:
			response = self.getResponse(url)
			if (self.isGood(response)):
				FLICKR[ "frob" ] = str(response["frob"]["_content"])
			else:
				self.reportError(response)
		except:			
			logging.error("Error: cannot get frob:" + str(sys.exc_info()))

	def getAuthKey(self):
		"""
		Checks to see if the user has authenticated this application
		"""
		d = {
			"frob"			: FLICKR[ "frob" ],
			"perms"		   : "delete"
			}
		sig = self.signCall(d)
		url = self.urlGen(api.auth, d, sig)
		ans = ""
		try:
			webbrowser.open(url)
			print("Copy-paste following URL into a web browser and follow instructions:")
			print(url)
			ans = raw_input("Have you authenticated this application? (Y/N): ")
		except:
			print(str(sys.exc_info()))
		if (ans.lower() == "n"):
			print("You need to allow this program to access your Flickr site.")
			print("Copy-paste following URL into a web browser and follow instructions:")
			print(url)
			print("After you have allowed access restart uploadr.py")
			sys.exit()

	def getToken(self):
		"""
		http://www.flickr.com/services/api/flickr.auth.getToken.html

		flickr.auth.getToken

		Returns the auth token for the given frob, if one has been attached. This method call must be signed.
		Authentication

		This method does not require authentication.
		Arguments

		NTC: We need to store the token in a file so we can get it and then check it insted of
		getting a new on all the time.

		"api_key" (Required)
		   Your API application key. See here for more details.
		frob (Required)
		   The frob to check.
		"""

		d = {
			"method"		  : "flickr.auth.getToken",
			"frob"			: str(FLICKR[ "frob" ]),
			"format"		  : "json",
			"nojsoncallback"  : "1"
		}
		sig = self.signCall(d)
		url = self.urlGen(api.rest, d, sig)
		try:
			res = self.getResponse(url)
			if (self.isGood(res)):
				self.token = str(res['auth']['token']['_content'])
				self.perms = str(res['auth']['perms']['_content'])
				self.cacheToken()
			else :
				self.reportError(res)
		except:
			logging.error(str(sys.exc_info()))

	def getCachedToken(self):
		"""
		Attempts to get the flickr token from disk.
	   """
		if (os.path.exists(TOKEN_PATH)):
			return open(TOKEN_PATH).read()
		else :
			return None

	def cacheToken(self):
		""" cacheToken
		"""

		try:
			open(TOKEN_PATH , "w").write(str(self.token))
		except:
			logging.error("Issue writing token to local cache " + str(sys.exc_info()))

	def checkToken(self):
		"""
		flickr.auth.checkToken

		Returns the credentials attached to an authentication token.
		Authentication

		This method does not require authentication.
		Arguments

		"api_key" (Required)
			Your API application key. See here for more details.
		auth_token (Required)
			The authentication token to check.
		"""

		if (self.token == None):
			return False
		else :
			d = {
				"auth_token"	  :  str(self.token) ,
				"method"		  :  "flickr.auth.checkToken",
				"format"		  : "json",
				"nojsoncallback"  : "1"
			}
			sig = self.signCall(d)

			url = self.urlGen(api.rest, d, sig)
			try:
				res = self.getResponse(url)
				if (self.isGood(res)):
					self.token = res['auth']['token']['_content']
					self.perms = res['auth']['perms']['_content']
					return True
				else :
					self.reportError(res)
			except:
				logging.error(str(sys.exc_info()))
			return False

	# Suppression des fichiers
	def removeDeletedMedia(self):
		""" Remove files deleted at the local source
		loop through database
		check if file exists
		if exists, continue
		if not exists, delete photo from fickr
		http://www.flickr.com/services/api/flickr.photos.delete.html
		"""

		self.debut("Removing deleted files")

		if (not self.checkToken()):
			self.authenticate()

		self.qry.execute("SELECT files_id, path FROM files")
		rows = self.qry.fetchall()

		for row in rows:
			# le fichier n'existe plus
			if(not os.path.isfile(row[1])):
				self.deleteFile(row[0], row[1])
				
		self.fin()
	
	def minuteleft(self):
		return ( time.time() - self.starttime ) / 60
		
	def isTooLong(self):
		res = False
		# Upload max
		if (MAX_FILES != 0):
			if ( self.step >= MAX_FILES ): 
				logging.info('Limit reached (max files = %d)' % MAX_FILES)
				res = True
		if ( MAX_MINUTES !=0):
			if ( self.minuteleft() > MAX_MINUTES ): 
				logging.info('Limit reached (max minutes = %d)' % MAX_MINUTES )			
				res = True
		return res
		
	def upload(self):
		logging.info("SYNC DIR=%s" % FILES_DIR)					
		# upload new files
		self.upload_new()
		if MANAGE_CHANGES:
			# upload changed files
			self.upload_changed()
		logging.info("Fichiers uploades=%d" % self.nbrficadd)	
		
	def upload_changed(self):	
		self.debut('files changed')
		self.step = 0		
		files = self.qry.execute("SELECT files_id, path, md5 FROM files", ())
		for row in files:
			if not self.stepIt(): break				
			# on ignore les fichiers que l on vient d ajouter
			if row[1] in self.uploaded: continue
			self.uploadChange(row[0], row[1], row[2] )					
		self.stepShow()
		self.fin()			
					
	def upload_new(self):	
		self.debut('Uploading files')
						
		# Tous les fichiers trouves
		allMedia = self.grabNewFiles()
		self.count = len(allMedia)
		logging.info("  files count=%d" % self.count )
									
		self.qry.execute("SELECT path FROM files")
		existingMedia = set(f[0] for f in self.qry.fetchall())				
		changedMedia = set(allMedia) - existingMedia

		self.newcount = len(changedMedia)			
		logging.info("  new files=%d" % self.newcount)

		# pour chaque fichier
#		for i, filename in enumerate(changedMedia):
		for filename in changedMedia:
			file_id = self.uploadFile(filename)
			if file_id == -1: continue
			self.db_fileadd( file_id, filename )			
			# Tags
#				self.addTagToPhoto( file_id, filename)
			# new set
			setName = self.getSetName(filename)		
			if self.lastset != setName:
				self.lastset = setName
				setid = self.addSet(setName, file_id)
				self.lastsetid = setid			
			# ajoute la photo dans le set
			self.addFileToSet(self.lastsetid, file_id, filename )			
			self.wait_drip()
			if self.isTooLong(): break
							
		self.fin()
		
	# Attente entre chaque transfert
	def wait_drip(self):
		if not args.drip_feed: return
		print("Waiting " + str(DRIP_TIME) + " seconds before next upload")
		time.sleep(DRIP_TIME)
	
	def sendRapport(self):
		rapport	 = "DIR: %s\n" % (FILES_DIR)		
		rapport	+= "  Files          = %d\n" % (self.count)
		rapport	+= "  Files news     = %d\n\n" % (self.newcount)
		rapport += "FILES:\n"
		rapport += "  Files added    = %d\n" % (self.nbrficadd)
		rapport += "  Files deleted  = %d\n" % (self.nbrficdel)
		rapport += "  Files replaced = %d\n\n" % (self.nbrficrep)
		rapport += "  Files tagged   = %d\n\n" % (self.nbrtag)		
		rapport += "SETS:\n"
		rapport += "  Sets added     = %d\n" % (self.nbrsetadd)
		rapport += "  Sets deleted   = %d\n\n" % (self.nbrsetdel)
		rapport += "TIME: %s\n" % sectostr(time.time() - self.starttime)
		logging.info(rapport)		
		if ( SMTP_USER != '' ) and ( SMTP_PASS != ''):		
			mailit.smtp_user = SMTP_USER
			mailit.smtp_pass = SMTP_PASS
			mailit.you       = SMTP_USER
			mailit.me        = SMTP_USER			
			mailit.send_mail("uploadr", rapport )
#			mailit.send_file("uploadr", logname )

	def convertRawFiles(self):
		""" convertRawFiles
		"""
		if (not CONVERT_RAW_FILES):
			return

		logging.info( "*****Converting files*****" )
		for ext in RAW_EXT:
			logging.info ("About to convert files with extension:" + ext + " files.")
		
			for dirpath, dirnames, filenames in os.walk(FILES_DIR, followlinks=True):
				for curr_dir in EXCLUDED_FOLDERS:
					if curr_dir in dirnames:
						dirnames.remove(curr_dir)
						
				for f in filenames :					
					fileExt = f.split(".")[-1]
					filename = f.split(".")[0]
					if (fileExt.lower() == ext):
						
						if (not os.path.exists(dirpath + "/" + filename + ".JPG")):
							logging.info("About to create JPG from raw " + dirpath + "/" + f)
							
							flag = ""
							if ext is "cr2":
								flag = "PreviewImage"
							else :
								flag = "JpgFromRaw"
							
							command = RAW_TOOL_PATH + "exiftool -b -" + flag + " -w .JPG -ext " + ext + " -r '" + dirpath + "/" + filename + "." + fileExt + "'"
					
							subprocess.call(command, shell=True)
						
						if (not os.path.exists(dirpath + "/" + filename + ".JPG_original")):
							logging.info ("About to copy tags from " + dirpath + "/" + f + " to JPG.")
						
							command = RAW_TOOL_PATH + "exiftool -tagsfromfile '" + dirpath + "/" + f + "' -r -all:all -ext JPG '" + dirpath + "/" + filename + ".JPG'"
							# print(command)
						
							subprocess.call(command, shell=True)
						
							logging.info ("Finished copying tags.")
			
			
			logging.info ("Finished converting files with extension:" + ext + ".")

		logging.info( "*****Completed converting files*****" )

	# recupere la liste des fichiers
	def grabNewFiles(self):
		""" grabNewFiles
		"""

		files = []
		for dirpath, dirnames, filenames in os.walk(FILES_DIR, followlinks=True):
			# les dossiers a exclure
			for curr_dir in EXCLUDED_FOLDERS:
				if curr_dir in dirnames:
					dirnames.remove(curr_dir)
			# les fichiers
			for f in filenames :
				if any(ignored.search(f) for ignored in IGNORED_REGEX):
					continue
				ext = f.lower().split(".")[-1]
				# les extensions autorisees
				if ext in ALLOWED_EXT:
					fileSize = os.path.getsize(dirpath + "/" + f)
					if (fileSize < FILE_MAX_SIZE):
						files.append(os.path.normpath(dirpath + "/" + f).replace("'", "\'"))
		files.sort()
		return files
		
	# Tags en fonctions du dossier
	def getSetName(self, filename):
		realTags = os.path.dirname(os.path.abspath(filename))
		realTags = realTags[len(ROOT_DIR):]
		return realTags
		
	# chaque dossier forme un TAG
	def getTags(self, filename):
		res = ''
		folderTag = self.getSetName(filename)
		folders = folderTag.split("/")
		for folder in folders:			
#			res += "%s " % folder.replace(" ", "_")
			res += "'%s' " % folder			
		return res


	def uploadFile(self, filename):
#		print("Uploading %s" % filename)
		try:
			size = os.path.getsize(filename)
			tags = self.getTags(filename)  				
			# les parametres
			if args.title:	   FLICKR["title"] = args.title
			if args.description: FLICKR["description"] = args.description
			if args.tags:		FLICKR["tags"] += " " + args.tags
			d = {
				"auth_token"	: str(self.token),
				"perms"		    : str(self.perms),
				"title"		    : str(FLICKR["title"]),
				"description"   : str(FLICKR["description"]),
				"tags"		    : str(FLICKR["tags"] + " " + tags),
				"is_public"	    : str(FLICKR["is_public"]),
				"is_friend"	    : str(FLICKR["is_friend"]),
				"is_family"	    : str(FLICKR["is_family"])
			}
			sig = self.signCall(d)
			d[ "api_sig" ] = sig
			d[ "api_key" ] = FLICKR[ "api_key" ]			
			# Envoi
			deb = time.time()												
			photo = ('photo', filename, open(filename, 'rb').read())					
			url = self.build_request(api.upload, d, (photo,))
			# Retour
			res = parse(urllib2.urlopen(url))
			if (not res == "" and res.documentElement.attributes['stat'].value == "ok"):
				ms  = time.time() - deb								
				self.nbrficadd += 1												
				self.trace('%d. Uploaded %s %s %s' %  ( self.nbrficadd, filename, sectostr(ms), kbpsToStr(size, ms) ) )
				# Add to DB				
				file_id = int(str(res.getElementsByTagName('photoid')[0].firstChild.nodeValue))								
				self.uploaded.append(filename)
				return file_id
			else:
				print("erreur uploadFile %s" % (filename) )
				print(res.toxml())
				return -1
		except:
			self.logError( "uploadFile %s" % (filename) )
			return -1

	def db_fileadd( self, file_id, filename ):
		try:
			self.qry.execute('INSERT INTO files (files_id, path, md5, tagged) VALUES (?, ?, ?, 1)',	(file_id, filename, self.md5Checksum(filename),) )
			self.cnx.commit()			
		except:
			self.logError( "db_fileadd %s" % (filename) )
				
	# Upload le fichier
	def uploadChange(self, file_id, filename, md5):
		fileMd5 = self.md5Checksum(filename)
		if (fileMd5 != str(md5)):
			self.replacePhoto(filename, file_id, fileMd5);		
			return True
		else:
			return False

	def replacePhoto(self, filename, file_id, fileMd5) :
		success = False
		logging.info("Replacing the file: " + filename)
		try:
			d = {
				"auth_token"	: str(self.token),
				"photo_id"	 : str(file_id)
			}
			sig = self.signCall(d)
			d[ "api_sig" ] = sig
			d[ "api_key" ] = FLICKR[ "api_key" ]
			# Envoi
			photo = ('photo', filename, open(filename, 'rb').read())			
			url = self.build_request(api.replace, d, (photo,))
			res = parse(urllib2.urlopen(url))
			if (not res == "" and res.documentElement.attributes['stat'].value == "ok"):
				# Add to set
				self.qry.execute('UPDATE files SET md5 = ? WHERE files_id = ?', (fileMd5, file_id))
				self.cnx.commit()
				success = True
				self.nbrficrep += 1				
			else :
				self.logError("A problem occurred while attempting to replace the file: " + filename)
				try:
					logging.error("Error: " + str(res.toxml()))
				except:
					pass
		except:
			self.logError('replacePhoto')

		return success


	def deleteSet(self, set_id ):
		success = False
		logging.info("Suppression Set=%s" % set_id )
		try:
			d = {
				"auth_token"	  : str(self.token),
				"perms"		   	  : str(self.perms),
				"format"		  : "rest",
				"method"		  : "flickr.photosets.delete",
				"photoset_id"	  : str(set_id),
				"format"		  : "json",
				"nojsoncallback"  : "1"
			}
			sig = self.signCall(d)
			url = self.urlGen(api.rest, d, sig)
			res = self.getResponse(url)
			if (self.isGood(res)):
				success = True
				self.nbrsetdel += 1
			else:
				# pas correctement supprime				
				if(res['code'] != 1):					
					self.reportError(res)
					self.reportError(res)
		except:
			self.logError('deleteSet')
		return success



	def deleteFile(self, file_id, filename ):
		success = False		
		self.trace("Suppression Photo=%s %s" % (file_id, filename))
		try:
			d = {
				"auth_token"	  : str(self.token),
				"perms"		      : str(self.perms),
				"format"		  : "rest",
				"method"		  : "flickr.photos.delete",
				"photo_id"	  	  : str(file_id),
				"format"		  : "json",
				"nojsoncallback"  : "1"
			}
			sig = self.signCall(d)
			url = self.urlGen(api.rest, d, sig)
			res = self.getResponse(url)
			if (self.isGood(res)):
				self.db_delete(file_id)
				success = True
				self.nbrficdel += 1				
			else :
				if(res['code'] == 1):
					# File already removed from Flicker				
					self.db_delete(file_id)
					self.nbrficdel += 1									
				else :
					self.reportError(res)
		except:
			self.logError('deleteFile')
		return success
		
	def db_delete(self, fileid):
		# Find out if the file is the last item in a set, if so, remove the set from the local db
		self.qry.execute("SELECT set_id FROM files WHERE files_id = ?", (fileid,))
		row = self.qry.fetchone()
		# fichier associe au dossier ?
		self.qry.execute("SELECT set_id FROM files WHERE set_id = ?", (row[0],))
		rows = self.qry.fetchall()
		# on supprime le dossier associe
		set_id = row[0]
		if(len(rows) == 1):
			self.trace("Suppression Set=%s" % (set_id))
			self.qry.execute("DELETE FROM sets WHERE set_id = ?", (set_id,))
			self.cnx.commit()			
			# on le supprime de flickr
			self.deleteSet(set_id)			
		# On supprime le ficher
		self.qry.execute("DELETE FROM files WHERE files_id = ?", (fileid,))
		self.cnx.commit()

				
	def db_SetAdd(self, setId, setName, primaryPhotoId):
#		logging.debug("db_SetAdd : " + str(setName))
		self.qry.execute("INSERT INTO sets (set_id, name, primary_photo_id) VALUES (?,?,?)", (setId, setName, primaryPhotoId))
		self.cnx.commit()		
		self.qry.execute("UPDATE files SET set_id = ? WHERE files_id = ?", (setId, primaryPhotoId))
		self.cnx.commit()
		return True

	# 
	def build_request(self, theurl, fields, files, txheaders=None):
		"""
		build_request/encode_multipart_formdata code is from www.voidspace.org.uk/atlantibots/pythonutils.html

		Given the fields to set and the files to encode it returns a fully formed urllib2.Request object.
		You can optionally pass in additional headers to encode into the opject. (Content-type and Content-length will be overridden if they are set).
		fields is a sequence of (name, value) elements for regular form fields - or a dictionary.
		files is a sequence of (name, filename, value) elements for data to be uploaded as files.
		"""

		content_type, body = self.encode_multipart_formdata(fields, files)
		if not txheaders: txheaders = {}
		txheaders['Content-type'] = content_type
		txheaders['Content-length'] = str(len(body))

		return urllib2.Request(theurl, body, txheaders)

	def encode_multipart_formdata(self, fields, files, BOUNDARY='-----' + mimetools.choose_boundary() + '-----'):
		""" Encodes fields and files for uploading.
		fields is a sequence of (name, value) elements for regular form fields - or a dictionary.
		files is a sequence of (name, filename, value) elements for data to be uploaded as files.
		Return (content_type, body) ready for urllib2.Request instance
		You can optionally pass in a boundary string to use or we'll let mimetools provide one.
		"""

		CRLF = '\r\n'
		L = []
		if isinstance(fields, dict):
			fields = fields.items()
		for (key, value) in fields:
			L.append('--' + BOUNDARY)
			L.append('Content-Disposition: form-data; name="%s"' % key)
			L.append('')
			L.append(value)
		for (key, filename, value) in files:
			filetype = mimetypes.guess_type(filename)[0] or 'application/octet-stream'
			L.append('--' + BOUNDARY)
			L.append('Content-Disposition: form-data; name="%s"; filename="%s"' % (key, filename))
			L.append('Content-Type: %s' % filetype)
			L.append('')
			L.append(value)
		L.append('--' + BOUNDARY + '--')
		L.append('')
		body = CRLF.join(L)
		content_type = 'multipart/form-data; boundary=%s' % BOUNDARY  # XXX what if no files are encoded
		return content_type, body

	def isGood(self, res):
		""" isGood
		"""

		if (not res == "" and res['stat'] == "ok"):
			return True
		else :
			return False

	def logError(self, msg):
		print( "[EXCEPT] %s" % msg)					
		print( "[EXCEPT] %s" % sys.exc_info()[1])			
		logging.error(msg)
		logging.error(sys.exc_info()[1])
		

	def reportError(self, res):
		try:
			print("Res Error: " + str(res['code'] + " " + res['message']))			
			logging.error("Res Error: " + str(res['code'] + " " + res['message']))
		except:
			print("Res Error: " + str(res))			
			logging.error("Res Error: " + str(res))

	def getResponse(self, url):
		"""
		Send the url and get a response.  Let errors float up
		"""

		try:
			res = urllib2.urlopen(url).read()
		except urllib2.HTTPError, e:
			print("getReponse=%s" % e.code)
		except urllib2.URLError, e:
			print("getReponse=%s" % e.args)
		return json.loads(res)

	def run(self):
		while (True):
			self.upload()
			print("Last check: " + str(time.asctime(time.localtime())))
			time.sleep(SLEEP_TIME)

	def trace(self, msg):
		print( msg )
		logging.info(msg)			

	def debut(self, msg):
		self.tps = time.time()
		self.trace("[START] %s" % msg)
		
	def fin(self):		
		sec  = time.time() - self.tps
		self.trace("[ END ] %s" % sectostr(sec) )
		
	def stepShow(self):
		if (self.step % 10 == 0):
			print("  %d files processed" % (self.step) )
		
	def stepIt(self):
		self.step += 1
		self.stepShow()
		return not self.isTooLong()
		
	def addSet(self, setName, file_id):
		# Le set existe ?
		self.qry.execute("SELECT set_id FROM sets WHERE name = ?", (setName,))
		row = self.qry.fetchone()			
		# le dossier n'existe pas, on le cree
		if row == None:
			# ajout a flick + db
			setId = self.createSet(setName, file_id)
		else:
			setId = row[0]
		return setId
			
	# creation des dossiers
	def createSets(self):
		self.debut('Creating Sets')

		self.qry.execute( "SELECT f.files_id, f.path, f.set_id, s.name"
		                + "  FROM files f" 
						+ "  LEFT OUTER JOIN sets s ON s.set_id = f.set_id"	)
		files = self.qry.fetchall()

		# pour chaque fichier
		for f in files:
			files_id = f[0]			
			filename = f[1]
			
			# On cree le SET
			setName = self.getSetName(filename)			

			# Le set existe ?
			self.qry.execute("SELECT set_id FROM sets WHERE name = ?", (setName,))
			st = self.qry.fetchone()
			
			# le dossier n'existe pas, on le cree
			if st == None:
				# ajout a flick + db
				setId = self.createSet(setName, files_id)
				# on l associe
				self.addFileToSet(setId, files_id, filename)
			# Le dossier existe								
			else :
				setId = st[0]								
				
				# pas de set associe au fichier
				if ( f[2] == None ) :
					print("adding file to set " + setName)
					# on l associe
					self.addFileToSet(setId, files_id, filename)
				# Le dossier a change
				elif setId != f[2] :
					print("moving file to set " + setName)
					self.qry.execute("UPDATE files SET set_id = ? WHERE files_id = ?", (setId, files_id))
					self.cnx.commit;
					# on supprime les anciens sets
					self.qry.execute("DELETE FROM sets WHERE set_id <> ? AND name = ?", (setId, setName))
					self.cnx.commit;					
					# on l'associe
					self.addFileToSet(setId, files_id, filename)
		self.fin()

	def db_filesetset(self, file_id, set_id):
		self.qry.execute("UPDATE files SET set_id = ? WHERE files_id = ?", (set_id, file_id))
		self.cnx.commit()							

	# association fichier set
	def addFileToSet(self, setId, file_id, filename):
		if setId == -1 : return
		try:
#			print('addFileToSet setid=%s file_id=%s filename=%s ' % (setId, file_id, filename) )
			d = {
				"auth_token"		  : str(self.token),
				"perms"			      : str(self.perms),
				"format"			  : "json",
				"nojsoncallback"	  : "1",
				"method"			  : "flickr.photosets.addPhoto",
				"photoset_id"		  : str(setId),
				"photo_id"			  : str(file_id)
			}
			sig = self.signCall(d)
			url = self.urlGen(api.rest, d, sig)
			res = self.getResponse(url)
			if (self.isGood(res)):
#				print("Successfully added file %s to its set." % (filename) )
				self.db_filesetset(file_id, setId)				
			else :
				if (res['code'] == 1) :
					setName = self.getSetName(filename)
					self.logError("Photoset ID=%s %s not found" % (setId, setName))								
#					self.createSet(setName, file_id)
				# Le set existe
				elif (res['code'] == 3) :
#					print("Successfully added file %s to its set." % (filename) )
					self.db_filesetset(file_id, setId)				
				else :
					print('addFileToSet')
					self.reportError(res)
		except:
			self.logError('addFileToSet')

	def createSet(self, setName, primaryPhotoId):
		print("Creating Set: %s" % setName )
		try:
			d = {
				"auth_token"		  : str(self.token),
				"perms"			      : str(self.perms),
				"format"			  : "json",
				"nojsoncallback"	  : "1",
				"method"			  : "flickr.photosets.create",
				"description"         : "autoupload",				
				"primary_photo_id"    : str(primaryPhotoId),
				"title"			      : setName
			}

			sig = self.signCall(d)
			url = self.urlGen(api.rest, d, sig)
			res = self.getResponse(url)
			if (self.isGood(res)):
				set_id = res["photoset"]["id"]
				self.db_SetAdd(set_id, setName, primaryPhotoId)
				self.nbrsetadd +=1
				return set_id
			else :
				logging.error(d)
				self.reportError(res)
		except:
			self.logError('createSet')
		return -1		

	def md5Checksum(self, filePath):
		with open(filePath, 'rb') as fh:
			m = hashlib.md5()
			while True:
				data = fh.read(8192)
				if not data:
					break
				m.update(data)
			return m.hexdigest()

	# Ajoute des tags a toutes photos
	def addTagsToAll(self) :
		self.addTagsToUploadedPhotos(True)

	# Ajoute des tags aux photos
	def addTagsToUploadedPhotos(self, allfiles = False) :
		self.debut('Adding tags to photos')		
		if allfiles:
			self.qry.execute("SELECT files_id, path, set_id, tagged FROM files")		
		else:		
			self.qry.execute("SELECT files_id, path, set_id, tagged FROM files WHERE tagged <> 1")
		files = self.qry.fetchall()
		for row in files:
			self.addTagToPhoto( row[0], row[1])
			if not self.stepIt(): break				
		self.stepShow()
		self.fin()

	# Ajout d'un tag
	def addTagToPhoto(self, file_id, filename) :
		tags = self.getTags(filename)  				
#		print( "Adding tag <%s> to photo: %s" % (tags, filename))
		try:
#			method = "flickr.photos.addTags"
			method = "flickr.photos.setTags"
			d = {
				"auth_token"		  : str(self.token),
				"perms"			      : str(self.perms),
				"format"			  : "json",
				"nojsoncallback"	  : "1",
				"method"			  : method,
				"photo_id"		  	  : str(file_id),
				"tags"			      : tags
			}
			sig = self.signCall(d)
			url = self.urlGen(api.rest, d, sig)
			res = self.getResponse(url)
			if (self.isGood(res)):
				self.db_tagged(file_id)
				self.nbrtag += 1
				return True
			else:
				self.logError("addTagToPhoto %s" % filename)
				self.reportError(res)
				return False				
		except:
			self.logError("addTagToPhoto %s" % filename)
			return False

	def db_tagged(self, file_id):
		self.qry.execute("UPDATE files SET tagged=1 WHERE files_id=? AND tagged=0", (file_id,))
		self.cnx.commit()
		

	# Supprime en base les dossiers qui ne sont plus utilises
	def removeUselessSetsTable(self) :
		self.debut('Removing empty Sets from DB')
		
		# @@@ suppression des dossiers absents
#		self.qry.execute("SELECT name FROM sets")
#		res = self.qry.fetchall()
#		for row in res:
#			dos = ROOT_DIR + str(row[0])
#			print(dos)
#			if not (os.path.exists( dos ) ):
#				print( 'absent %s' % ( dos ) )
				
		self.qry.execute("SELECT set_id, name FROM sets WHERE set_id NOT IN (SELECT set_id FROM files)")
		unusedsets = self.qry.fetchall()

		for row in unusedsets:
			self.trace("delete set:" + str(row[0]) + "(" + row[1] + ")")
			self.qry.execute("DELETE FROM sets WHERE set_id = ?", (row[0],))
			self.cnx.commit()

		self.fin()

	# Display Sets
	def displaySets(self) :
		self.qry.execute("SELECT set_id, name FROM sets")
		allsets = self.qry.fetchall()
		for row in allsets:
			print("DB Set=%s %s" % (row[0], row[1]))


	# Get sets from Flickr
	def FlickrRemoveAll(self):
		self.debut('FlickrRemoveAll')
		self.qry.execute("DELETE FROM sets", ())
		self.qry.execute("DELETE FROM files", ())
		self.cnx.commit()
		try:
			d = {
				"auth_token"		  : str(self.token),
				"perms"			   : str(self.perms),
				"format"			  : "json",
				"nojsoncallback"	  : "1",
				"method"			  : "flickr.photosets.getList"
			}
			url = self.urlGen(api.rest, d, self.signCall(d))
			res = self.getResponse(url)
			if (self.isGood(res)):				
				for row in res['photosets']['photoset']:
					setId = row['id']					
#					print('delete set %s' % setId)					
					self.deleteSet(setId)			
		except:
			self.logError('FlickrRemoveAll')
		self.fin()


	# Get sets from Flickr
	def getFlickrSets(self):
		self.debut('Adding Flickr Sets to DB')
# {u'date_update': u'1393089867', u'visibility_can_see_set': 1, u'description': {u'_content': u''}, u'videos': 0, u'title': {u'_content': u'Tenerife'}, u'farm': 6, u'needs_interstitial': 0, u'primary': u'12698498025', u'server': u'5500', u'date_create': u'1393085789', u'photos': u'3', u'secret': u'728aa9caf9', u'count_comments': u'0', u'count_views': u'1', u'can_comment': 1, u'id': u'72157641357634265'}		
		try:
			d = {
				"auth_token"		  : str(self.token),
				"perms"			      : str(self.perms),
				"format"			  : "json",
				"nojsoncallback"	  : "1",
				"method"			  : "flickr.photosets.getList"
			}
			url = self.urlGen(api.rest, d, self.signCall(d))
			res = self.getResponse(url)
			if (self.isGood(res)):
				for row in res['photosets']['photoset']:
					setId = row['id']
					setName = row['title']['_content']
					desc = row['description']['_content'] 
#					print( 'FlickR Set=%s %s' % ( setId, setName ) )
					# on ne recupere que les dossiers charges en auto
					if desc == 'autoupload':
						primaryPhotoId = row['primary']
						self.qry.execute("SELECT set_id FROM sets WHERE set_id = '" + setId + "'")
						foundSets = self.qry.fetchone()
						if foundSets == None:
							logging.info("Adding set %s %s %s" % (setId, setName, primaryPhotoId))
							self.qry.execute("INSERT INTO sets (set_id, name, primary_photo_id) VALUES (?,?,?)", (setId, setName, primaryPhotoId))
							self.cnx.commit()
			else:
				print(d)
				logging.error(d)
				self.reportError(res)
		except:
			self.logError('getFlickrSets')
		self.fin()


#=====
# MAIN
#=====
logging.info("--------- START ---------")				
print("--------- Start time: " + time.strftime("%c") + " ---------");
if __name__ == "__main__":
	# Ensure that only once instance of this script is running
	f = open (LOCK_PATH, 'w')
	try: fcntl.lockf (f, fcntl.LOCK_EX | fcntl.LOCK_NB)
	except IOError, e:
		if e.errno == errno.EAGAIN:
			sys.stderr.write('[%s] Script already running.\n' % time.strftime ('%c'))
			sys.exit(-1)
		raise
		
	# ini
	if FILES_DIR == "":
		print("Please configure the name of the folder in the script with media available to sync with Flickr.")
		sys.exit()

	if FLICKR["api_key"] == "" or FLICKR["secret"] == "":
		print("Please enter an API key and secret in the script file (see README).")
		sys.exit()
		
	# Les parametres
	parser = argparse.ArgumentParser(description='Upload files to Flickr.')
	parser.add_argument('-d', 	'--daemon', 	action='store_true',	help='Run forever as a daemon')
	parser.add_argument('-i', 	'--title', 		action='store',			help='Title for uploaded files')
	parser.add_argument('-e', 	'--description', action='store',		help='Description for uploaded files')
	parser.add_argument('-t', 	'--tags', 		action='store', 		help='Space-separated tags for uploaded files')
	parser.add_argument('-r', 	'--drip-feed',	action='store_true', 	help='Wait a bit between uploading individual files')	
	parser.add_argument('-raz', '--raz', 		action='store_true', 	help='delete all file in database and all flickr set')
	parser.add_argument('-tst', '--tst', 		action='store_true', 	help='test')
	parser.add_argument('-tagall', '--tagall', 	action='store_true', 	help='tag all photos')	
	args = parser.parse_args()
	
	# la classe
	flick = Uploadr()	

	if (not flick.checkToken()):
		flick.authenticate()
				
	#------
	# DEBUG
	#------
	if args.tst:
		print('* * * TEST * * *')
		MAX_MINUTES = 1
#		flick.removeDeletedMedia()					
#		flick.getFlickrSets()
#		flick.removeUselessSetsTable()		
#		flick.convertRawFiles()
#		flick.upload()
#		flick.upload()
#		flick.removeUselessSetsTable()				
#		flick.createSets()
#		flick.addTagsToAll()
		flick.addTagToPhoto( 16200998513, "/volume2/Photos/A manger recette/_Plat principal/Choucroute/2011/IMG_1984.JPG")
	#-------		
	# DEAMON
	#-------		
	elif args.daemon:
		flick.run()		
	#-----------		
	# DELETE ALL
	#-----------
	elif args.raz:
		print('* * * PURGE * * *')		
#		flick.getFlickrSets()		
#		flick.FlickrRemoveAll()		
#		flick.displaySets()
	#--------------
	# TAG ALL FILES
	#--------------
	elif args.tagall:
		flick.addTagsToAll()	
	#-----
	# MAIN
	#-----
	else:
		flick.removeDeletedMedia()					
		flick.getFlickrSets()
		flick.removeUselessSetsTable()		
		flick.convertRawFiles()
		flick.upload()

	# Rapport par mail
	flick.sendRapport()
print("--------- End time: " + time.strftime("%c") + " ---------");
logging.info("--------- END ---------")				



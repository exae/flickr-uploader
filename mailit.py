#!/usr/bin/env python

from smtplib import SMTP_SSL as SMTP
from email.mime.text import MIMEText
from email.MIMEMultipart import MIMEMultipart

me  = ""
you = ""
smtp_host = "smtp.gmail.com"
smtp_port = 465
smtp_user = ""
smtp_pass = ""

def send_mail(sujet, text):
	msg = MIMEMultipart()	
	msg['Subject'] = sujet
	msg['From'] = me
	msg['To'] = you	
	msg.attach(MIMEText(text))	
	s = SMTP(host=smtp_host, port=smtp_port )
	s.login(smtp_user, smtp_pass )		
	s.sendmail(me, [you], msg.as_string())
	s.quit()

def send_file(sujet, filename):
	# the text file contains only ASCII characters.
	fp = open(filename, 'rb')
	msg = MIMEText(fp.read())
	fp.close()
	
	msg['Subject'] = sujet
	msg['From'] = me
	msg['To'] = you
	
	s = SMTP(host=smtp_host, port=smtp_port )
	s.login(smtp_user, smtp_pass )	
	s.sendmail(me, [you], msg.as_string())
	s.quit()


#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# GAM
#
# Copyright 2015, LLC All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
u"""GAM is a command line tool which allows Administrators to control their G Suite domain and accounts.

With GAM you can programatically create users, turn on/off services for users like POP and Forwarding and much more.
For more information, see https://github.com/taers232c/GAM-N
"""

__author__ = u'Ross Scroggs <ross.scroggs@gmail.com>'
__version__ = u'4.03.15'
__license__ = u'Apache License 2.0 (http://www.apache.org/licenses/LICENSE-2.0)'

import sys
import os
import string
import time
import base64
import codecs
import collections
import ConfigParser
import csv
import datetime
from htmlentitydefs import name2codepoint
from HTMLParser import HTMLParser
import json
import mimetypes
import platform
import random
import re
import socket
import StringIO

import googleapiclient
import googleapiclient.discovery
import googleapiclient.errors
import googleapiclient.http
import httplib2
from iso8601 import iso8601
import oauth2client.client
import oauth2client.service_account
import oauth2client.file
import oauth2client.tools

# Override some oauth2client.tools strings saving us a few GAM-specific mods to oauth2client
oauth2client.tools._FAILED_START_MESSAGE = """
Failed to start a local webserver listening on either port 8080
or port 8090. Please check your firewall settings and locally
running programs that may be blocking or using those ports.

Falling back to nobrowser.txt  and continuing with
authorization.
"""

oauth2client.tools._BROWSER_OPENED_MESSAGE = """
Your browser has been opened to visit:

    {address}

If your browser is on a different machine then press CTRL+C and
create a file called nobrowser.txt in the same folder as GAM.
"""

oauth2client.tools._GO_TO_LINK_MESSAGE = """
Go to the following link in your browser:

    {address}
"""

GAM = u'GAM-N'
GAM_URL = u'https://github.com/taers232c/{0}'.format(GAM)
GAM_INFO = u'GAM {0} - {1} / {2} / Python {3}.{4}.{5} {6} / {7} {8} /'.format(__version__, GAM_URL,
                                                                              __author__,
                                                                              sys.version_info[0], sys.version_info[1], sys.version_info[2],
                                                                              sys.version_info[3],
                                                                              platform.platform(), platform.machine())
GAM_RELEASES = u'https://github.com/taers232c/{0}/releases'.format(GAM)
GAM_WIKI = u'https://github.com/jay0lee/GAM/wiki'
GAM_ALL_RELEASES = u'https://api.github.com/repos/taers232c/'+GAM+u'/releases'
GAM_LATEST_RELEASE = GAM_ALL_RELEASES+u'/latest'

TRUE = u'true'
FALSE = u'false'
TRUE_VALUES = [TRUE, u'on', u'yes', u'enabled', u'1']
FALSE_VALUES = [FALSE, u'off', u'no', u'disabled', u'0']
TRUE_FALSE = [TRUE, FALSE]
usergroup_types = [u'user', u'users', u'group', u'ou', u'org', u'ou_and_children', u'ou_and_child', u'query',
                   u'license', u'licenses', u'licence', u'licences', u'courseparticipants', u'teachers', u'students',
                   u'file', u'csv', u'csvfile', u'all', u'cros']
ERROR = u'ERROR'
ERROR_PREFIX = ERROR+u': '
WARNING = u'WARNING'
WARNING_PREFIX = WARNING+u': '
DEFAULT_CHARSET = [u'mbcs', u'utf-8'][os.name != u'nt']
ONE_KILO_BYTES = 1000
ONE_MEGA_BYTES = 1000000
ONE_GIGA_BYTES = 1000000000
SECONDS_PER_MINUTE = 60
SECONDS_PER_HOUR = 3600
SECONDS_PER_DAY = 86400
FN_CLIENT_SECRETS_JSON = u'client_secrets.json'
FN_EXTRA_ARGS_TXT = u'extra-args.txt'
FN_LAST_UPDATE_CHECK_TXT = u'lastupdatecheck.txt'
FN_OAUTH2SERVICE_JSON = u'oauth2service.json'
FN_OAUTH2_TXT = u'oauth2.txt'
MY_CUSTOMER = u'my_customer'

# Global variables

# CL_argv is a copy of sys.argv
# CL_argvI is an index into CL_argv
# CL_argvLen is len(CL_arvgv)
CL_argv = []
CL_argvI = 0
CL_argvLen = 0
# The following GM_XXX constants are arbitrary but must be unique
# Most errors print a message and bail out with a return code
# Some commands want to set a non-zero return code but not bail
GM_SYSEXITRC = u'sxrc'
# Path to gam
GM_GAM_PATH = u'gpth'
# Are we on Windows?
GM_WINDOWS = u'wndo'
# Encodings
GM_SYS_ENCODING = u'syen'
# Extra arguments to pass to GAPI functions
GM_EXTRA_ARGS_LIST = u'exad'
# Current API user
GM_CURRENT_API_USER = u'capu'
# Current API scope
GM_CURRENT_API_SCOPES = u'scoc'
# Values retrieved from oauth2service.json
GM_OAUTH2SERVICE_JSON_DATA = u'oajd'
GM_OAUTH2SERVICE_ACCOUNT_CLIENT_ID = u'oaci'
# File containing time of last GAM update check
GM_LAST_UPDATE_CHECK_TXT = u'lupc'
# Dictionary mapping OrgUnit ID to Name
GM_MAP_ORGUNIT_ID_TO_NAME = u'oi2n'
# Dictionary mapping Role ID to Name
GM_MAP_ROLE_ID_TO_NAME = u'ri2n'
# Dictionary mapping Role Name to ID
GM_MAP_ROLE_NAME_TO_ID = u'rn2i'
# Dictionary mapping User ID to Name
GM_MAP_USER_ID_TO_NAME = u'ui2n'
# GAM cache directory. If no_cache is True, this variable will be set to None
GM_CACHE_DIR = u'gacd'
# Reset GAM cache directory after discovery
GM_CACHE_DISCOVERY_ONLY = u'gcdo'
#
GM_Globals = {
  GM_SYSEXITRC: 0,
  GM_GAM_PATH: os.path.dirname(os.path.realpath(__file__)) if not getattr(sys, u'frozen', False) else os.path.dirname(sys.executable),
  GM_WINDOWS: os.name == u'nt',
  GM_SYS_ENCODING: DEFAULT_CHARSET,
  GM_EXTRA_ARGS_LIST:  [(u'prettyPrint', False)],
  GM_CURRENT_API_USER: None,
  GM_CURRENT_API_SCOPES: [],
  GM_OAUTH2SERVICE_JSON_DATA: None,
  GM_OAUTH2SERVICE_ACCOUNT_CLIENT_ID: None,
  GM_LAST_UPDATE_CHECK_TXT: u'',
  GM_MAP_ORGUNIT_ID_TO_NAME: None,
  GM_MAP_ROLE_ID_TO_NAME: None,
  GM_MAP_ROLE_NAME_TO_ID: None,
  GM_MAP_USER_ID_TO_NAME: None,
  GM_CACHE_DIR: None,
  GM_CACHE_DISCOVERY_ONLY: False,
  }
#
# Global variables defined by environment variables/signal files
#
# When retrieving lists of Google Drive activities from API, how many should be retrieved in each chunk
GC_ACTIVITY_MAX_RESULTS = u'activity_max_results'
# Automatically generate gam batch command if number of users specified in gam users xxx command exceeds this number
# Default: 0, don't automatically generate gam batch commands
GC_AUTO_BATCH_MIN = u'auto_batch_min'
# GAM cache directory
GC_CACHE_DIR = u'cache_dir'
# Character set of batch, csv, data files
GC_CHARSET = u'charset'
# Path to client_secrets.json
GC_CLIENT_SECRETS_JSON = u'client_secrets_json'
# GAM config directory containing client_secrets.json, oauth2.txt, oauth2service.json, extra_args.txt
GC_CONFIG_DIR = u'config_dir'
# Column delimiter in CSV input file
GC_CSV_INPUT_COLUMN_DELIMITER = u'csv_input_column_delimiter'
# Convert newlines in text fields to "\n" in CSV output file
GC_CSV_OUTPUT_CONVERT_CR_NL = u'csv_output_convert_cr_nl'
# Column delimiter in CSV output file
GC_CSV_OUTPUT_COLUMN_DELIMITER = u'csv_output_column_delimiter'
# Field list delimiter in CSV output file
GC_CSV_OUTPUT_FIELD_DELIMITER = u'csv_output_field_delimiter'
# custmerId from gam.cfg or retrieved from Google
GC_CUSTOMER_ID = u'customer_id'
# If debug_level > 0: extra_args[u'prettyPrint'] = True, httplib2.debuglevel = gam_debug_level, appsObj.debug = True
GC_DEBUG_LEVEL = u'debug_level'
# When retrieving lists of ChromeOS/Mobile devices from API, how many should be retrieved in each chunk
GC_DEVICE_MAX_RESULTS = u'device_max_results'
# Domain obtained from gam.cfg or oauth2.txt
GC_DOMAIN = u'domain'
# Google Drive download directory
GC_DRIVE_DIR = u'drive_dir'
# When retrieving lists of Drive files/folders from API, how many should be retrieved in each chunk
GC_DRIVE_MAX_RESULTS = u'drive_max_results'
# Path to extra_args.txt
GC_EXTRA_ARGS = u'extra_args'
# When retrieving lists of Google Group members from API, how many should be retrieved in each chunk
GC_MEMBER_MAX_RESULTS = u'member_max_results'
# If no_browser is False, writeCSVfile won't open a browser when todrive is set
# and doOAuthRequest prints a link and waits for the verification code when oauth2.txt is being created
GC_NO_BROWSER = u'no_browser'
# Disable GAM API caching
GC_NO_CACHE = u'no_cache'
# Disable GAM update check
GC_NO_UPDATE_CHECK = u'no_update_check'
# Disable SSL certificate validation
GC_NO_VERIFY_SSL = u'no_verify_ssl'
# Number of threads for gam batch
GC_NUM_THREADS = u'num_threads'
# Path to oauth2.txt
GC_OAUTH2_TXT = u'oauth2_txt'
# Path to oauth2service.json
GC_OAUTH2SERVICE_JSON = u'oauth2service_json'
# Convert newlines in text fields to "\n" in show commands
GC_SHOW_CONVERT_CR_NL = u'show_convert_cr_nl'
# When retrieving lists of Users from API, how many should be retrieved in each chunk
GC_USER_MAX_RESULTS = u'user_max_results'

GC_Defaults = {
  GC_ACTIVITY_MAX_RESULTS: 100,
  GC_AUTO_BATCH_MIN: 0,
  GC_CACHE_DIR: u'',
  GC_CHARSET: DEFAULT_CHARSET,
  GC_CLIENT_SECRETS_JSON: FN_CLIENT_SECRETS_JSON,
  GC_CONFIG_DIR: u'',
  GC_CSV_INPUT_COLUMN_DELIMITER: u',',
  GC_CSV_OUTPUT_CONVERT_CR_NL: FALSE,
  GC_CSV_OUTPUT_COLUMN_DELIMITER: u',',
  GC_CSV_OUTPUT_FIELD_DELIMITER: u' ',
  GC_CUSTOMER_ID: MY_CUSTOMER,
  GC_DEBUG_LEVEL: 0,
  GC_DEVICE_MAX_RESULTS: 500,
  GC_DOMAIN: u'',
  GC_DRIVE_DIR: u'',
  GC_DRIVE_MAX_RESULTS: 1000,
  GC_EXTRA_ARGS: u'',
  GC_MEMBER_MAX_RESULTS: 200,
  GC_NO_BROWSER: False,
  GC_NO_CACHE: False,
  GC_NO_UPDATE_CHECK: False,
  GC_NO_VERIFY_SSL: False,
  GC_NUM_THREADS: 25,
  GC_OAUTH2_TXT: FN_OAUTH2_TXT,
  GC_OAUTH2SERVICE_JSON: FN_OAUTH2SERVICE_JSON,
  GC_SHOW_CONVERT_CR_NL: FALSE,
  GC_USER_MAX_RESULTS: 500,
  }

GC_Values = {}

GC_TYPE_BOOLEAN = u'bool'
GC_TYPE_CHOICE = u'choi'
GC_TYPE_DIRECTORY = u'dire'
GC_TYPE_EMAIL = u'emai'
GC_TYPE_FILE = u'file'
GC_TYPE_INTEGER = u'inte'
GC_TYPE_LANGUAGE = u'lang'
GC_TYPE_STRING = u'stri'

GC_VAR_TYPE = u'type'
GC_VAR_ENVVAR = u'enva'
GC_VAR_LIMITS = u'lmit'
GC_VAR_SFFT = u'sfft'
GC_VAR_SIGFILE = u'sigf'

GC_VAR_INFO = {
  GC_ACTIVITY_MAX_RESULTS: {GC_VAR_TYPE: GC_TYPE_INTEGER, GC_VAR_ENVVAR: u'GAM_ACTIVITY_MAX_RESULTS', GC_VAR_LIMITS: (1, 500)},
  GC_AUTO_BATCH_MIN: {GC_VAR_TYPE: GC_TYPE_INTEGER, GC_VAR_ENVVAR: u'GAM_AUTOBATCH', GC_VAR_LIMITS: (None, None)},
  GC_CACHE_DIR: {GC_VAR_TYPE: GC_TYPE_DIRECTORY, GC_VAR_ENVVAR: u'GAMCACHEDIR'},
  GC_CHARSET: {GC_VAR_TYPE: GC_TYPE_STRING, GC_VAR_ENVVAR: u'GAM_CHARSET'},
  GC_CLIENT_SECRETS_JSON: {GC_VAR_TYPE: GC_TYPE_FILE, GC_VAR_ENVVAR: u'CLIENTSECRETS'},
  GC_CONFIG_DIR: {GC_VAR_TYPE: GC_TYPE_DIRECTORY, GC_VAR_ENVVAR: u'GAMUSERCONFIGDIR'},
  GC_CSV_INPUT_COLUMN_DELIMITER: {GC_VAR_TYPE: GC_TYPE_STRING, GC_VAR_ENVVAR: u'GAM_CSV_INPUT_COLUMN_DELIMITER', GC_VAR_LIMITS: (1, 1)},
  GC_CSV_OUTPUT_CONVERT_CR_NL: {GC_VAR_TYPE: GC_TYPE_BOOLEAN, GC_VAR_ENVVAR: u'GAM_CSV_OUTPUT_CONVERT_CR_NL', GC_VAR_SFFT: (FALSE, TRUE)},
  GC_CSV_OUTPUT_COLUMN_DELIMITER: {GC_VAR_TYPE: GC_TYPE_STRING, GC_VAR_ENVVAR: u'GAM_CSV_OUTPUT_COLUMN_DELIMITER', GC_VAR_LIMITS: (1, 1)},
  GC_CSV_OUTPUT_FIELD_DELIMITER: {GC_VAR_TYPE: GC_TYPE_STRING, GC_VAR_ENVVAR: u'GAM_CSV_OUTPUT_FIELD_DELIMITER', GC_VAR_LIMITS: (1, 1)},
  GC_CUSTOMER_ID: {GC_VAR_TYPE: GC_TYPE_STRING, GC_VAR_ENVVAR: u'CUSTOMER_ID'},
  GC_DEBUG_LEVEL: {GC_VAR_TYPE: GC_TYPE_INTEGER, GC_VAR_SIGFILE: u'debug.gam', GC_VAR_LIMITS: (0, None), GC_VAR_SFFT: (0, 4)},
  GC_DEVICE_MAX_RESULTS: {GC_VAR_TYPE: GC_TYPE_INTEGER, GC_VAR_ENVVAR: u'GAM_DEVICE_MAX_RESULTS', GC_VAR_LIMITS: (1, 1000)},
  GC_DOMAIN: {GC_VAR_TYPE: GC_TYPE_STRING, GC_VAR_ENVVAR: u'GA_DOMAIN'},
  GC_DRIVE_DIR: {GC_VAR_TYPE: GC_TYPE_DIRECTORY, GC_VAR_ENVVAR: u'GAMDRIVEDIR'},
  GC_DRIVE_MAX_RESULTS: {GC_VAR_TYPE: GC_TYPE_INTEGER, GC_VAR_ENVVAR: u'GAM_DRIVE_MAX_RESULTS', GC_VAR_LIMITS: (1, 1000)},
  GC_EXTRA_ARGS: {GC_VAR_TYPE: GC_TYPE_FILE, GC_VAR_SIGFILE: FN_EXTRA_ARGS_TXT, GC_VAR_SFFT: (u'', FN_EXTRA_ARGS_TXT)},
  GC_MEMBER_MAX_RESULTS: {GC_VAR_TYPE: GC_TYPE_INTEGER, GC_VAR_ENVVAR: u'GAM_MEMBER_MAX_RESULTS', GC_VAR_LIMITS: (1, 10000)},
  GC_NO_BROWSER: {GC_VAR_TYPE: GC_TYPE_BOOLEAN, GC_VAR_SIGFILE: u'nobrowser.txt', GC_VAR_SFFT: (False, True)},
  GC_NO_CACHE: {GC_VAR_TYPE: GC_TYPE_BOOLEAN, GC_VAR_SIGFILE: u'nocache.txt', GC_VAR_SFFT: (False, True)},
  GC_NO_UPDATE_CHECK: {GC_VAR_TYPE: GC_TYPE_BOOLEAN, GC_VAR_SIGFILE: u'noupdatecheck.txt', GC_VAR_SFFT: (False, True)},
  GC_NO_VERIFY_SSL: {GC_VAR_TYPE: GC_TYPE_BOOLEAN, GC_VAR_SIGFILE: u'noverifyssl.txt', GC_VAR_SFFT: (False, True)},
  GC_NUM_THREADS: {GC_VAR_TYPE: GC_TYPE_INTEGER, GC_VAR_ENVVAR: u'GAM_THREADS', GC_VAR_LIMITS: (1, None)},
  GC_OAUTH2_TXT: {GC_VAR_TYPE: GC_TYPE_FILE, GC_VAR_ENVVAR: u'OAUTHFILE'},
  GC_OAUTH2SERVICE_JSON: {GC_VAR_TYPE: GC_TYPE_FILE, GC_VAR_ENVVAR: u'OAUTHSERVICEFILE'},
  GC_SHOW_CONVERT_CR_NL: {GC_VAR_TYPE: GC_TYPE_BOOLEAN, GC_VAR_ENVVAR: u'GAM_SHOW_CONVERT_CR_NL', GC_VAR_SFFT: (FALSE, TRUE)},
  GC_USER_MAX_RESULTS: {GC_VAR_TYPE: GC_TYPE_INTEGER, GC_VAR_ENVVAR: u'GAM_USER_MAX_RESULTS', GC_VAR_LIMITS: (1, 500)},
  }

# Google API constants
APPLICATION_VND_GOOGLE_APPS = u'application/vnd.google-apps.'
MIMETYPE_GA_DOCUMENT = APPLICATION_VND_GOOGLE_APPS+u'document'
MIMETYPE_GA_DRAWING = APPLICATION_VND_GOOGLE_APPS+u'drawing'
MIMETYPE_GA_FOLDER = APPLICATION_VND_GOOGLE_APPS+u'folder'
MIMETYPE_GA_FORM = APPLICATION_VND_GOOGLE_APPS+u'form'
MIMETYPE_GA_FUSIONTABLE = APPLICATION_VND_GOOGLE_APPS+u'fusiontable'
MIMETYPE_GA_MAP = APPLICATION_VND_GOOGLE_APPS+u'map'
MIMETYPE_GA_PRESENTATION = APPLICATION_VND_GOOGLE_APPS+u'presentation'
MIMETYPE_GA_SCRIPT = APPLICATION_VND_GOOGLE_APPS+u'script'
MIMETYPE_GA_SITES = APPLICATION_VND_GOOGLE_APPS+u'sites'
MIMETYPE_GA_SPREADSHEET = APPLICATION_VND_GOOGLE_APPS+u'spreadsheet'

NEVER_TIME = u'1970-01-01T00:00:00.000Z'
NEVER_START_DATE = u'1970-01-01'
NEVER_END_DATE = u'1969-12-31'
ROLE_MANAGER = u'MANAGER'
ROLE_MEMBER = u'MEMBER'
ROLE_OWNER = u'OWNER'
ROLE_USER = u'USER'
PROJECTION_CHOICES_MAP = {u'basic': u'BASIC', u'full': u'FULL',}
SORTORDER_CHOICES_MAP = {u'ascending': u'ASCENDING', u'descending': u'DESCENDING',}
ME_IN_OWNERS = u"'me' in owners"
ME_IN_OWNERS_AND = ME_IN_OWNERS+u" and "

# Valid language codes
LANGUAGE_CODES_MAP = {
  u'af': u'af', #Afrikaans
  u'am': u'am', #Amharic
  u'ar': u'ar', #Arabica
  u'az': u'az', #Azerbaijani
  u'bg': u'bg', #Bulgarian
  u'bn': u'bn', #Bengali
  u'ca': u'ca', #Catalan
  u'chr': u'chr', #Cherokee
  u'cs': u'cs', #Czech
  u'cy': u'cy', #Welsh
  u'da': u'da', #Danish
  u'de': u'de', #German
  u'el': u'el', #Greek
  u'en': u'en', #English
  u'en-gb': u'en-GB', #English (UK)
  u'en-us': u'en-US', #English (US)
  u'es': u'es', #Spanish
  u'es-419': u'es-419', #Spanish (Latin America)
  u'et': u'et', #Estonian
  u'eu': u'eu', #Basque
  u'fa': u'fa', #Persian
  u'fi': u'fi', #Finnish
  u'fr': u'fr', #French
  u'fr-ca': u'fr-ca', #French (Canada)
  u'ag': u'ga', #Irish
  u'gl': u'gl', #Galician
  u'gu': u'gu', #Gujarati
  u'he': u'he', #Hebrew
  u'hi': u'hi', #Hindi
  u'hr': u'hr', #Croatian
  u'hu': u'hu', #Hungarian
  u'hy': u'hy', #Armenian
  u'id': u'id', #Indonesian
  u'in': u'in',
  u'is': u'is', #Icelandic
  u'it': u'it', #Italian
  u'iw': u'he', #Hebrew
  u'ja': u'ja', #Japanese
  u'ka': u'ka', #Georgian
  u'km': u'km', #Khmer
  u'kn': u'kn', #Kannada
  u'ko': u'ko', #Korean
  u'lo': u'lo', #Lao
  u'lt': u'lt', #Lithuanian
  u'lv': u'lv', #Latvian
  u'ml': u'ml', #Malayalam
  u'mn': u'mn', #Mongolian
  u'mr': u'mr', #Marathi
  u'ms': u'ms', #Malay
  u'my': u'my', #Burmese
  u'ne': u'ne', #Nepali
  u'nl': u'nl', #Dutch
  u'no': u'no', #Norwegian
  u'or': u'or', #Oriya
  u'pl': u'pl', #Polish
  u'pt-br': u'pt-BR', #Portuguese (Brazil)
  u'pt-pt': u'pt-PT', #Portuguese (Portugal)
  u'ro': u'ro', #Romanian
  u'ru': u'ru', #Russian
  u'si': u'si', #Sinhala
  u'sk': u'sk', #Slovak
  u'sl': u'sl', #Slovenian
  u'sr': u'sr', #Serbian
  u'sv': u'sv', #Swedish
  u'sw': u'sw', #Swahili
  u'ta': u'ta', #Tamil
  u'te': u'te', #Telugu
  u'th': u'th', #Thai
  u'tl': u'tl', #Tagalog
  u'tr': u'tr', #Turkish
  u'uk': u'uk', #Ukrainian
  u'ur': u'ur', #Urdu
  u'vi': u'vi', #Vietnamese
  u'zh-cn': u'zh-CN', #Chinese (Simplified)
  u'zh-hk': u'zh-HK', #Chinese (Hong Kong/Traditional)
  u'zh-tw': u'zh-TW', #Chinese (Taiwan/Traditional)
  u'zu': u'zu', #Zulu
  }
# GAPI APIs
GAPI_ADMIN_SETTINGS_API = u'admin-settings'
GAPI_APPSACTIVITY_API = u'appsactivity'
GAPI_CALENDAR_API = u'calendar'
GAPI_CLASSROOM_API = u'classroom'
GAPI_CLOUDPRINT_API = u'cloudprint'
GAPI_DATATRANSFER_API = u'datatransfer'
GAPI_DIRECTORY_API = u'directory'
GAPI_DRIVE_API = u'drive'
GAPI_EMAIL_SETTINGS_API = u'email-settings'
GAPI_GMAIL_API = u'gmail'
GAPI_GPLUS_API = u'plus'
GAPI_GROUPSSETTINGS_API = u'groupssettings'
GAPI_LICENSING_API = u'licensing'
GAPI_OAUTH2_API = u'oauth2'
GAPI_REPORTS_API = u'reports'
GAPI_SITEVERIFICATION_API = u'siteVerification'
# GDATA APIs
GDATA_ADMIN_SETTINGS_API = GAPI_ADMIN_SETTINGS_API
GDATA_EMAIL_AUDIT_API = u'email-audit'
GDATA_EMAIL_SETTINGS_API = GAPI_EMAIL_SETTINGS_API
GDATA_SITES_API = u'sites'
# callGData throw errors
GDATA_BAD_GATEWAY = 601
GDATA_BAD_REQUEST = 602
GDATA_DOES_NOT_EXIST = 1301
GDATA_ENTITY_EXISTS = 1300
GDATA_FORBIDDEN = 603
GDATA_INSUFFICIENT_PERMISSIONS = 604
GDATA_INTERNAL_SERVER_ERROR = 1000
GDATA_INVALID_DOMAIN = 605
GDATA_INVALID_VALUE = 1801
GDATA_NAME_NOT_VALID = 1303
GDATA_NOT_FOUND = 606
GDATA_PRECONDITION_FAILED = 607
GDATA_QUOTA_EXCEEDED = 608
GDATA_SERVICE_NOT_APPLICABLE = 1410
GDATA_SERVICE_UNAVAILABLE = 609
GDATA_TOKEN_EXPIRED = 610
GDATA_TOKEN_INVALID = 403
GDATA_UNKNOWN_ERROR = 600
#
GDATA_NON_TERMINATING_ERRORS = [GDATA_BAD_GATEWAY, GDATA_QUOTA_EXCEEDED, GDATA_SERVICE_UNAVAILABLE, GDATA_TOKEN_EXPIRED]
GDATA_EMAILSETTINGS_THROW_LIST = [GDATA_INVALID_DOMAIN, GDATA_DOES_NOT_EXIST, GDATA_SERVICE_NOT_APPLICABLE, GDATA_BAD_REQUEST, GDATA_NAME_NOT_VALID, GDATA_INTERNAL_SERVER_ERROR, GDATA_INVALID_VALUE]
# oauth errors
OAUTH2_TOKEN_ERRORS = [u'access_denied', u'invalid_grant', u'unauthorized_client: Unauthorized client or scope in request.', u'access_denied: Requested client not authorized.',
                       u'invalid_grant: Not a valid email.', u'invalid_grant: Invalid email or User ID', u'invalid_grant: Bad Request',
                       u'invalid_request: Invalid impersonation prn email address.', u'internal_failure: Backend Error']
# callGAPI throw reasons
GAPI_ABORTED = u'aborted'
GAPI_ALREADY_EXISTS = u'alreadyExists'
GAPI_AUTH_ERROR = u'authError'
GAPI_BACKEND_ERROR = u'backendError'
GAPI_BAD_REQUEST = u'badRequest'
GAPI_CANNOT_CHANGE_OWN_ACL = u'cannotChangeOwnAcl'
GAPI_CANNOT_CHANGE_OWNER_ACL = u'cannotChangeOwnerAcl'
GAPI_CANNOT_DELETE_PRIMARY_CALENDAR = u'cannotDeletePrimaryCalendar'
GAPI_CANNOT_DELETE_PRIMARY_SENDAS = u'cannotDeletePrimarySendAs'
GAPI_CONDITION_NOT_MET = u'conditionNotMet'
GAPI_CUSTOMER_NOT_FOUND = u'customerNotFound'
GAPI_CYCLIC_MEMBERSHIPS_NOT_ALLOWED = u'cyclicMembershipsNotAllowed'
GAPI_DELETED = u'deleted'
GAPI_DELETED_USER_NOT_FOUND = u'deletedUserNotFound'
GAPI_DOMAIN_ALIAS_NOT_FOUND = u'domainAliasNotFound'
GAPI_DOMAIN_NOT_FOUND = u'domainNotFound'
GAPI_DOMAIN_NOT_VERIFIED_SECONDARY = u'domainNotVerifiedSecondary'
GAPI_DUPLICATE = u'duplicate'
GAPI_FAILED_PRECONDITION = u'failedPrecondition'
GAPI_FILE_NOT_FOUND = u'fileNotFound'
GAPI_FORBIDDEN = u'forbidden'
GAPI_GROUP_NOT_FOUND = u'groupNotFound'
GAPI_INSUFFICIENT_PERMISSIONS = u'insufficientPermissions'
GAPI_INTERNAL_ERROR = u'internalError'
GAPI_INVALID = u'invalid'
GAPI_INVALID_ARGUMENT = u'invalidArgument'
GAPI_INVALID_CUSTOMER_ID = u'invalidCustomerId'
GAPI_INVALID_INPUT = u'invalidInput'
GAPI_INVALID_MEMBER = u'invalidMember'
GAPI_INVALID_ORGUNIT = u'invalidOrgunit'
GAPI_INVALID_PARENT_ORGUNIT = u'invalidParentOrgunit'
GAPI_INVALID_QUERY = u'invalidQuery'
GAPI_INVALID_RESOURCE = u'invalidResource'
GAPI_INVALID_SCHEMA_VALUE = u'invalidSchemaValue'
GAPI_INVALID_SCOPE_VALUE = u'invalidScopeValue'
GAPI_INVALID_SHARING_REQUEST = u'invalidSharingRequest'
GAPI_LOGIN_REQUIRED = u'loginRequired'
GAPI_MEMBER_NOT_FOUND = u'memberNotFound'
GAPI_NOT_FOUND = u'notFound'
GAPI_NOT_IMPLEMENTED = u'notImplemented'
GAPI_ORGUNIT_NOT_FOUND = u'orgunitNotFound'
GAPI_PERMISSION_DENIED = u'permissionDenied'
GAPI_PERMISSION_NOT_FOUND = u'permissionNotFound'
GAPI_PHOTO_NOT_FOUND = u'photoNotFound'
GAPI_QUOTA_EXCEEDED = u'quotaExceeded'
GAPI_RATE_LIMIT_EXCEEDED = u'rateLimitExceeded'
GAPI_REQUIRED = u'required'
GAPI_RESOURCE_ID_NOT_FOUND = u'resourceIdNotFound'
GAPI_RESOURCE_NOT_FOUND = u'resourceNotFound'
GAPI_SERVICE_LIMIT = u'serviceLimit'
GAPI_SERVICE_NOT_AVAILABLE = u'serviceNotAvailable'
GAPI_SYSTEM_ERROR = u'systemError'
GAPI_TIME_RANGE_EMPTY = u'timeRangeEmpty'
GAPI_UNKNOWN_ERROR = u'unknownError'
GAPI_USER_NOT_FOUND = u'userNotFound'
GAPI_USER_RATE_LIMIT_EXCEEDED = u'userRateLimitExceeded'
#
GCP_CANT_MODIFY_FINISHED_JOB = u'Can\'t modify the finished job.'
GCP_FAILED_TO_SHARE_THE_PRINTER = u'Failed to share the printer.'
GCP_NO_PRINT_JOBS = u'No print job available on specified printer.'
GCP_UNKNOWN_JOB_ID = u'Unknown job id.'
GCP_UNKNOWN_PRINTER = u'Unknown printer.'
GCP_USER_IS_NOT_AUTHORIZED = u'User is not authorized.'
#
GAPI_DEFAULT_RETRY_REASONS = [GAPI_QUOTA_EXCEEDED, GAPI_RATE_LIMIT_EXCEEDED, GAPI_USER_RATE_LIMIT_EXCEEDED, GAPI_BACKEND_ERROR, GAPI_INTERNAL_ERROR]
GAPI_ACTIVITY_THROW_REASONS = [GAPI_SERVICE_NOT_AVAILABLE]
GAPI_CALENDAR_THROW_REASONS = [GAPI_SERVICE_NOT_AVAILABLE, GAPI_AUTH_ERROR]
GAPI_DRIVE_THROW_REASONS = [GAPI_SERVICE_NOT_AVAILABLE, GAPI_AUTH_ERROR]
GAPI_GMAIL_THROW_REASONS = [GAPI_SERVICE_NOT_AVAILABLE, GAPI_BAD_REQUEST]
GAPI_GPLUS_THROW_REASONS = [GAPI_SERVICE_NOT_AVAILABLE]
GAPI_USER_GET_THROW_REASONS = [GAPI_USER_NOT_FOUND, GAPI_DOMAIN_NOT_FOUND, GAPI_FORBIDDEN, GAPI_BAD_REQUEST, GAPI_BACKEND_ERROR, GAPI_SYSTEM_ERROR]
#
DRIVE_API_VERSION = u'v2'
#
DRIVE_FILE_NAME = u'title'
DRIVE_FILE_VIEW_LINK = u'alternateLink'
DRIVE_FILES_LIST = u'items'
DRIVE_CREATE_FILE = u'insert'
DRIVE_PATCH_FILE = u'patch'
DRIVE_UPDATE_FILE = u'update'
#
DRIVE_PERMISSIONS_NAME = u'name'
DRIVE_PERMISSIONS_LIST = u'items'
DRIVE_CREATE_PERMISSIONS = u'insert'
DRIVE_PATCH_PERMISSIONS = u'patch'
#
DRIVE_REVISIONS_LIST = u'items'
#
DFA_LOCALFILEPATH = u'localFilepath'
DFA_LOCALFILENAME = u'localFilename'
DFA_LOCALMIMETYPE = u'localMimeType'
DFA_CONVERT = u'convert'
DFA_OCR = u'ocr'
DFA_OCRLANGUAGE = u'ocrLanguage'
DFA_PARENTQUERY = u'parentQuery'
DFA_ADD_PARENTS = u'addParents'
DFA_REMOVE_PARENTS = u'removeParents'
# Object BNF names
OB_ACCESS_TOKEN = u'AccessToken'
OB_ARGUMENT = u'argument'
OB_ASP_ID = u'AspID'
OB_CALENDAR_ACL_ROLE = u'CalendarACLRole'
OB_CHAR_SET = u'CharacterSet'
OB_CIDR_NETMASK = u'CIDRnetmask'
OB_CLIENT_ID = u'ClientID'
OB_COURSE_ALIAS = u'CourseAlias'
OB_COURSE_ALIAS_LIST = u'CourseAliasList'
OB_COURSE_ENTITY = u'CourseEntity'
OB_COURSE_ID = u'CourseID'
OB_CROS_DEVICE_ENTITY = u'CrOSDeviceEntity'
OB_CROS_ENTITY = u'CrOSEntity'
OB_CUSTOMER_ID = u'CustomerID'
OB_DOMAIN_ALIAS = u'DomainAlias'
OB_DOMAIN_NAME = u'DomainName'
OB_DRIVE_FILE_ENTITY = u'DriveFileEntity'
OB_DRIVE_FILE_ID = u'DriveFileID'
OB_DRIVE_FILE_NAME = u'DriveFileName'
OB_DRIVE_FOLDER_ID = u'DriveFolderID'
OB_DRIVE_FOLDER_NAME = u'DriveFolderName'
OB_EMAIL_ADDRESS = u'EmailAddress'
OB_EMAIL_ADDRESS_ENTITY = u'EmailAddressEntity'
OB_EMAIL_ADDRESS_OR_UID = u'EmailAaddress|UniqueID'
OB_ENTITY = u'Entity'
OB_ENTITY_TYPE = u'EntityType'
OB_EVENT_ID = u'EventID'
OB_FIELD_NAME = u'FieldName'
OB_FIELD_NAME_LIST = "FieldNameList"
OB_FILE_NAME = u'FileName'
OB_FILE_NAME_FIELD_NAME = OB_FILE_NAME+u'(:'+OB_FIELD_NAME+u')+'
OB_FILE_NAME_OR_URL = u'FileName|URL'
OB_FILE_PATH = u'FilePath'
OB_FILTER_ID = u'FilterID'
OB_FORMAT_LIST = u'FormatList'
OB_GAM_ARGUMENT_LIST = u'GAM argument list'
OB_GROUP_ENTITY = u'GroupEntity'
OB_GROUP_ITEM = u'GroupItem'
OB_GUARDIAN_ITEM = U'GuardianItem'
OB_GUARDIAN_INVITATION_ID = U'GuardianInvitationID'
OB_GUARDIAN_STATE_LIST = u'GuardianStateList'
OB_HOST_NAME = u'HostName'
OB_JOB_ID = u'JobID'
OB_JOB_OR_PRINTER_ID = u'JobID|PrinterID'
OB_LABEL_NAME = u'LabelName'
OB_LABEL_REPLACEMENT = u'LabelReplacement'
OB_MOBILE_DEVICE_ENTITY = u'MobileDeviceEntity'
OB_MOBILE_ENTITY = u'MobileEntity'
OB_NAME = u'Name'
OB_NOTIFICATION_ID = u'NotificationID'
OB_PARAMETER_KEY = u'ParameterKey'
OB_PARAMETER_VALUE = u'ParameterValue'
OB_ORGUNIT_PATH = u'OrgUnitPath'
OB_ORGUNIT_ENTITY = u'OrgUnitEntity'
OB_PERMISSION_ID = u'PermissionID'
OB_PHOTO_FILENAME_PATTERN = u'FilenameNamePattern'
OB_PRINTER_ID = u'PrinterID'
OB_PRINTER_ID_LIST = u'PrinterIDList'
OB_PRINTJOB_AGE = u'PrintJobAge'
OB_PRINTJOB_ID = u'PrintJobID'
OB_PRODUCT_ID_LIST = u'ProductIDList'
OB_PROPERTY_KEY = u'PropertyKey'
OB_PROPERTY_VALUE = u'PropertyValue'
OB_QUERY = u'Query'
OB_RECURRENCE = u'RRULE EXRULE RDATE and EXDATE lines'
OB_REQUEST_ID = u'RequestID'
OB_RESOURCE_ENTITY = u'ResourceEntity'
OB_RESOURCE_ID = u'ResourceID'
OB_RE_PATTERN = u'REPattern'
OB_ROLE_ASSIGNMENT_ID = u'RoleAssignmentId'
OB_ROLE_ID = u'RoleId'
OB_SCHEMA_ENTITY = u'SchemaEntity'
OB_SCHEMA_NAME = u'SchemaName'
OB_SCHEMA_NAME_FIELD_NAME = u'SchemaName.FieldName'
OB_SCHEMA_NAME_LIST = u'SchemaNameList'
OB_SECTION_NAME = u'SectionName'
OB_SERVICE_NAME = u'ServiceName'
OB_SKU_ID = u'SKUID'
OB_SKU_ID_LIST = u'SKUIDList'
OB_STRING = u'String'
OB_STUDENT_ITEM = u'StudentItem'
OB_TAG = u'Tag'
OB_TRANSFER_ID = u'TransferID'
OB_URI = u'URI'
OB_URL = u'URL'
OB_USER_ENTITY = u'UserEntity'
OB_USER_ITEM = u'UserItem'

# Command line batch/csv keywords
GAM_CMD = u'gam'
COMMIT_BATCH_CMD = u'commit-batch'
#
CLEAR_NONE_ARGUMENT = [u'clear', u'none',]
CLIENTID_ARGUMENT = [u'clientid',]
COLUMN_DELIMITER_ARGUMENT = [u'columndelimiter',]
DATAFIELD_ARGUMENT = [u'datafield',]
DATA_ARGUMENT = [u'data',]
DELIMITER_ARGUMENT = [u'delimiter',]
FILE_ARGUMENT = [u'file',]
FROM_ARGUMENT = [u'from',]
IDFIRST_ARGUMENT = [u'idfirst',]
IDS_ARGUMENT = [u'ids',]
ID_ARGUMENT = [u'id',]
KEYFIELD_ARGUMENT = [u'keyfield',]
LOGO_ARGUMENT = [u'logo',]
MATCHFIELD_ARGUMENT = [u'matchfield',]
MODE_ARGUMENT = [u'mode',]
MOVE_ADD_ARGUMENT = [u'move', u'add',]
MULTIVALUE_ARGUMENT = [u'multivalued', u'multivalue', u'value',]
NOINFO_ARGUMENT = [u'noinfo',]
NORMALIZE_ARGUMENT = [u'normalize',]
NOTSUSPENDED_ARGUMENT = [u'notsuspended',]
ORG_OU_ARGUMENT = [u'org', u'ou',]
PRIMARY_ARGUMENT = [u'primary',]
PRIMARY_NOTPRIMARY_CHOICE_MAP = {u'primary': True, u'notprimary': False}
QUERY_ARGUMENT = [u'query',]
SHOWTITLES_ARGUMENT = [u'showtitles',]
TODRIVE_ARGUMENT = [u'todrive',]
TO_ARGUMENT = [u'to',]
UNSTRUCTURED_FORMATTED_ARGUMENT = [u'unstructured', u'formatted',]

# These values can be translated into other languages
PHRASE_ACCESS_FORBIDDEN = u'Access Forbidden'
PHRASE_ACTION_APPLIED = u'Action Applied'
PHRASE_ADMIN_STATUS_CHANGED_TO = u'Admin Status Changed to'
PHRASE_ALL = u'All'
PHRASE_ALREADY_EXISTS_USE_MERGE_ARGUMENT = u'Already exists; use the "merge" argument to merge the labels'
PHRASE_AUTHORIZED = u'Authorized'
PHRASE_BAD_REQUEST = u'Bad Request'
PHRASE_CAN_NOT_BE_DOWNLOADED = u'Can not be downloaded'
PHRASE_CAN_NOT_CHANGE_OWNER_ACL = u'Can not change owner ACL'
PHRASE_CHECKING = u'Checking'
PHRASE_COMPLETE = u'Complete'
PHRASE_CONTAINS_AT_LEAST_1_ITEM = u'Contains at least 1 item'
PHRASE_COUNT_N_EXCEEDS_MAX_TO_PROCESS_M = u'Count {0} exceeds maximum to {1} {2}'
PHRASE_DATA_UPLOADED_TO_DRIVE_FILE = u'Data uploaded to Drive File'
PHRASE_DELEGATE_ACCESS_TO = u'Delegate Access to'
PHRASE_DENIED = u'DENIED'
PHRASE_DIRECTLY_IN_THE = u' directly in the {0}'
PHRASE_DOES_NOT_EXIST = u'Does not exist'
PHRASE_DOES_NOT_EXIST_OR_HAS_INVALID_FORMAT = u'Does not exist or has invalid format'
PHRASE_DOES_NOT_EXIST_OR_NOT_ALLOWED = u'Does not exist or not allowed'
PHRASE_DOMAIN_NOT_VERIFIED_SECONDARY = u'Domain is not a verified secondary domain'
PHRASE_DO_NOT_EXIST = u'Do not exist'
PHRASE_DUPLICATE = u'Duplicate'
PHRASE_EITHER = u'Either'
PHRASE_ENTITY_DOES_NOT_EXIST = u'{0} does not exist'
PHRASE_ERROR = u'error'
PHRASE_EXPECTED = u'Expected'
PHRASE_FAILED_TO_PARSE_AS_JSON = u'Failed to parse as JSON'
PHRASE_FIELD_NOT_FOUND_IN_SCHEMA = u'Field {0} not found in schema {1}'
PHRASE_FINISHED = u'Finished'
PHRASE_FOR = u'for'
PHRASE_FORMAT_NOT_AVAILABLE = u'Format ({0}) not available'
PHRASE_FORMAT_NOT_DOWNLOADABLE = u'Format not downloadable'
PHRASE_FROM = u'From'
PHRASE_GETTING = u'Getting'
PHRASE_GETTING_ALL = u'Getting all'
PHRASE_GOOGLE_EARLIEST_REPORT_TIME = u'Google earliest report time'
PHRASE_GOT = u'Got'
PHRASE_HAS_CHILD_ORGS = 'Has child {0}'
PHRASE_INVALID = u'Invalid'
PHRASE_INVALID_ALIAS = u'Invalid Alias'
PHRASE_INVALID_CUSTOMER_ID = u'Invalid Customer ID'
PHRASE_INVALID_DOMAIN = u'Invalid Domain'
PHRASE_INVALID_PATH = u'Invalid Path'
PHRASE_INVALID_QUERY = u'Invalid Query'
PHRASE_INVALID_REQUEST = u'Invalid Request'
PHRASE_INVALID_ROLE = u'Invalid Role'
PHRASE_INVALID_SCHEMA_VALUE = u'Invalid Schema Value'
PHRASE_INVALID_SCOPE = u'Invalid Scope'
PHRASE_INVALID_SITE = u'Invalid Site ({0}), must match pattern ({1})'
PHRASE_IS_REQD_TO_CHG_PWD_NO_DELEGATION = u'is required to change password at next login. You must change password or clear changepassword flag for delegation.'
PHRASE_IS_SUSPENDED_NO_DELEGATION = u'is suspended. You must unsuspend for delegation.'
PHRASE_LABELS_NOT_FOUND = u'Labels ({0}) not found'
PHRASE_LIST = u'List'
PHRASE_LOOKING_UP_GOOGLE_UNIQUE_ID = u'Looking up Google Unique ID'
PHRASE_MARKED_AS = u'Marked as'
PHRASE_MAXIMUM_OF = u'maximum of'
PHRASE_MATCHED_THE_FOLLOWING = u'Matched the following'
PHRASE_MAY_TAKE_SOME_TIME_ON_A_LARGE = u'may take some time on a large'
PHRASE_NESTED_LOOP_CMD_NOT_ALLOWED = u'Command can not be nested.'
PHRASE_NEW_OWNER_MUST_DIFFER_FROM_OLD_OWNER = u'New owner must differ from old owner'
PHRASE_NON_BLANK = u'Non-blank'
PHRASE_NON_EMPTY = u'Non-empty'
PHRASE_NOT_A = u'Not a'
PHRASE_NOT_ALLOWED = u'Not Allowed'
PHRASE_NOT_FOUND = u'Not Found'
PHRASE_NOW_THE_PRIMARY_DOMAIN = u'Now the primary domain'
PHRASE_NO_ENTITIES_MATCHED = u'No {0} matched'
PHRASE_NO_FILTER_CRITERIA = U'No {0} criteria specified'
PHRASE_NO_FILTER_ACTIONS = U'No {0} actions specified'
PHRASE_NO_LABELS_MATCH = u'No Labels match'
PHRASE_NO_MESSAGES_WITH_LABEL = u'No Messages with Label'
PHRASE_NO_PRINT_JOBS = u'No Print Jobs'
PHRASE_NOT_REQUESTED = u'Not requested'
PHRASE_ONLY_ONE_OWNER_ALLOWED = u'Only one owner allowed'
PHRASE_OR = u'or'
PHRASE_PATH_NOT_AVAILABLE = u'Path not available'
PHRASE_PLEASE_SELECT_USER_TO_UNDELETE = u'Please select the correct one to undelete and specify with "gam undelete user uid:<uid>"'
PHRASE_SELECTED = u'Selected'
PHRASE_SERVICE_NOT_APPLICABLE = u'Service not applicable/Does not exist'
PHRASE_STARTING_N_WORKER_THREADS = u'Starting {0} worker threads...\n'
PHRASE_STARTING_THREAD = u'Starting thread'
PHRASE_STRING_LENGTH = u'string length'
PHRASE_THAT_MATCHED_QUERY = u'that matched query'
PHRASE_THAT_MATCH_QUERY = u'that match query'
PHRASE_TO = u'To'
PHRASE_UNKNOWN = u'Unknown'
PHRASE_UNKNOWN_COMMAND_SELECTOR = u'Unknown command or selector'
PHRASE_USE_DOIT_ARGUMENT_TO_PERFORM_ACTION = u'Use the "doit" argument to perform action'
PHRASE_USE_RECURSIVE_ARGUMENT_TO_COPY_FOLDERS = u'Use "recursive" argument to copy folders'
PHRASE_WAITING_FOR_PROCESSES_TO_COMPLETE = u'Waiting for running processes to finish before proceeding...'
PHRASE_WITH = u'with'
PHRASE_WOULD_MAKE_MEMBERSHIP_CYCLE = u'Would make membership cycle'

MESSAGE_API_ACCESS_CONFIG = u'API access is configured in your Control Panel under: Security-Show more-Advanced settings-Manage API client access'
MESSAGE_API_ACCESS_DENIED = u'API access Denied.\n\nPlease make sure the Client ID: {0} is authorized for the API Scope(s): {1}'
MESSAGE_BATCH_CSV_DASH_DEBUG_INCOMPATIBLE = u'"gam {0} - ..." is not compatible with debugging. Disable debugging by deleting debug.gam'
MESSAGE_GAM_EXITING_FOR_UPDATE = u'GAM is now exiting so that you can overwrite this old version with the latest release'
MESSAGE_GAM_OUT_OF_MEMORY = u'GAM has run out of memory. If this is a large G Suite instance, you should use a 64-bit version of GAM on Windows or a 64-bit version of Python on other systems.'
MESSAGE_HEADER_NOT_FOUND_IN_CSV_HEADERS = u'Header "{0}" not found in CSV headers of "{1}".'
MESSAGE_HIT_CONTROL_C_TO_UPDATE = u'\n\nHit CTRL+C to visit the GAM website and download the latest release or wait 15 seconds continue with this boring old version. GAM won\'t bother you with this announcement for 1 week or you can create a file named noupdatecheck.txt in the same location as gam.py or gam.exe and GAM won\'t ever check for updates.'
MESSAGE_INVALID_JSON = u'The file {0} has an invalid format.'
MESSAGE_NO_DISCOVERY_INFORMATION = u'No online discovery doc and {0} does not exist locally'
MESSAGE_NO_PYTHON_SSL = u'You don\'t have the Python SSL module installed so we can\'t verify SSL Certificates. You can fix this by installing the Python SSL module or you can live on the edge and turn SSL validation off by creating a file named noverifyssl.txt in the same location as gam.exe / gam.py'
MESSAGE_NO_TRANSFER_LACK_OF_DISK_SPACE = u'Cowardly refusing to perform migration due to lack of target drive space. Source size: {0}mb Target Free: {1}mb'
MESSAGE_REFUSING_TO_DEPROVISION_DEVICES = u'Refusing to deprovision {0} devices because acknowledge_device_touch_requirement not specified.\nDeprovisioning a device means the device will have to be physically wiped and re-enrolled to be managed by your domain again.\nThis requires physical access to the device and is very time consuming to perform for each device.\nPlease add "acknowledge_device_touch_requirement" to the GAM command if you understand this and wish to proceed with the deprovision.\nPlease also be aware that deprovisioning can have an effect on your device license count.\nSee https://support.google.com/chrome/a/answer/3523633 for full details.'
MESSAGE_REQUEST_COMPLETED_NO_FILES = u'Request completed but no results/files were returned, try requesting again'
MESSAGE_REQUEST_NOT_COMPLETE = u'Request needs to be completed before downloading, current status is: {0}'
MESSAGE_RESULTS_TOO_LARGE_FOR_GOOGLE_SPREADSHEET = u'Results are too large for Google Spreadsheets. Uploading as a regular CSV file.'
MESSAGE_SERVICE_NOT_APPLICABLE = u'Service not applicable for this address: {0}. Please make sure service is enabled for user and run\n\ngam user <user> check serviceaccount\n\nfor further instructions'
MESSAGE_INSTRUCTIONS_OAUTH2SERVICE_JSON = u'Please run\n\ngam create project\ngam user <user> check serviceaccount\n\nto create and configure a service account.'
MESSAGE_OAUTH2SERVICE_JSON_INVALID = u'The file {0} is missing required keys (client_email, client_id or private_key). Please remove it and recreate with the commands:\n\ngam create project\ngam user <user> check serviceaccount'

# Error message types; keys into ARGUMENT_ERROR_NAMES; arbitrary values but must be unique
ARGUMENT_BLANK = u'blnk'
ARGUMENT_EMPTY = u'empt'
ARGUMENT_EXTRANEOUS = u'extr'
ARGUMENT_INVALID = u'inva'
ARGUMENT_MISSING = u'miss'
#
# ARGUMENT_ERROR_NAMES[0] is plural,ARGUMENT_ERROR_NAMES[1] is singular
# These values can be translated into other languages
ARGUMENT_ERROR_NAMES = {
  ARGUMENT_BLANK: [u'Blank arguments', u'Blank argument'],
  ARGUMENT_EMPTY: [u'Empty arguments', u'Empty argument'],
  ARGUMENT_EXTRANEOUS: [u'Extra arguments', u'Extra argument'],
  ARGUMENT_INVALID: [u'Invalid arguments', u'Invalid argument'],
  ARGUMENT_MISSING: [u'Missing arguments', u'Missing argument'],
  }
# Program return codes
UNKNOWN_ERROR_RC = 1
USAGE_ERROR_RC = 2
SOCKET_ERROR_RC = 3
GOOGLE_API_ERROR_RC = 4
NETWORK_ERROR_RC = 5
FILE_ERROR_RC = 6
MEMORY_ERROR_RC = 7
KEYBOARD_INTERRUPT_RC = 8
HTTP_ERROR_RC = 9
NO_DISCOVERY_INFORMATION_RC = 11
API_ACCESS_DENIED_RC = 12
CONFIG_ERROR_RC = 13
CERTIFICATE_VALIDATION_UNSUPPORTED_RC = 14
NO_SCOPES_FOR_API_RC = 15
CLIENT_SECRETS_JSON_REQUIRED_RC = 16
OAUTH2SERVICE_JSON_REQUIRED_RC = 16
OAUTH2_TXT_REQUIRED_RC = 16
INVALID_JSON_RC = 17
AUTHENTICATION_TOKEN_REFRESH_ERROR_RC = 18
HARD_ERROR_RC = 19
# Information
ENTITY_IS_A_USER_RC = 20
ENTITY_IS_A_USER_ALIAS_RC = 21
ENTITY_IS_A_GROUP_RC = 22
ENTITY_IS_A_GROUP_ALIAS_RC = 23
# Warnings/Errors
AC_FAILED_RC = 50
AC_NOT_PERFORMED_RC = 51
BAD_REQUEST_RC = 53
DATA_NOT_AVALIABLE_RC = 55
ENTITY_DOES_NOT_EXIST_RC = 56
ENTITY_DUPLICATE_RC = 57
ENTITY_IS_NOT_AN_ALIAS_RC = 58
ENTITY_IS_UKNOWN_RC = 59
NO_ENTITIES_FOUND = 60
INVALID_DOMAIN_RC = 61
INVALID_DOMAIN_VALUE_RC = 62
INVALID_TOKEN_RC = 63
JSON_LOADS_ERROR_RC = 64
MULTIPLE_DELETED_USERS_FOUND_RC = 65
NO_CSV_HEADERS_ERROR_RC = 66
INSUFFICIENT_PERMISSIONS_RC = 67
REQUEST_COMPLETED_NO_RESULTS_RC = 71
REQUEST_NOT_COMPLETED_RC = 72
SERVICE_NOT_APPLICABLE_RC = 73
TARGET_DRIVE_SPACE_ERROR_RC = 74
USER_REQUIRED_TO_CHANGE_PASSWORD_ERROR_RC = 75
USER_SUSPENDED_ERROR_RC = 76

def convertUTF8(data):
  if isinstance(data, str):
    return data
  if isinstance(data, unicode):
    if GM_Globals[GM_WINDOWS]:
      return data
    return data.encode(GM_Globals[GM_SYS_ENCODING])
  if isinstance(data, collections.Mapping):
    return dict(map(convertUTF8, data.iteritems()))
  if isinstance(data, collections.Iterable):
    return type(data)(map(convertUTF8, data))
  return data

class _DeHTMLParser(HTMLParser):
  def __init__(self):
    HTMLParser.__init__(self)
    self.__text = []

  def handle_data(self, data):
    self.__text.append(data)

  def handle_charref(self, name):
    self.__text.append(unichr(int(name[1:], 16)) if name.startswith('x') else unichr(int(name)))

  def handle_entityref(self, name):
    cp = name2codepoint.get(name)
    if cp:
      self.__text.append(unichr(cp))
    else:
      self.__text.append(u'&'+name)

  def handle_starttag(self, tag, attrs):
    if tag == 'p':
      self.__text.append('\n\n')
    elif tag == 'br':
      self.__text.append('\n')
    elif tag == 'a':
      for attr in attrs:
        if attr[0] == 'href':
          self.__text.append('({0}) '.format(attr[1]))
          break
    elif tag == 'div':
      if not attrs:
        self.__text.append('\n')
    elif tag in ['http:', 'https']:
      self.__text.append(' ({0}//{1}) '.format(tag, attrs[0][0]))

  def handle_startendtag(self, tag, attrs):
    if tag == 'br':
      self.__text.append('\n\n')

  def text(self):
    return re.sub(r'\n{2}\n+', '\n\n', re.sub(r'\n +', '\n', ''.join(self.__text))).strip()

def dehtml(text):
  try:
    parser = _DeHTMLParser()
    parser.feed(text.encode(u'utf-8'))
    parser.close()
    return parser.text()
  except:
    from traceback import print_exc
    print_exc(file=sys.stderr)
    return text

# Concatenate list members, any item containing spaces is enclosed in ''
def makeQuotedList(items):
  qstr = u''
  for item in items:
    if item and (item.find(u' ') == -1) and (item.find(u',') == -1):
      qstr += item
    else:
      qstr += u"'"+item+u"'"
    qstr += u' '
  return qstr[:-1] if len(qstr) > 0 else u''

# Format a key value list
#   key, value	-> "key: value" + ", " if not last item
#   key, ''	-> "key:" + ", " if not last item
#   key, None	-> "key" + " " if not last item
def formatKeyValueList(prefixStr, kvList, suffixStr):
  msg = prefixStr
  i = 0
  l = len(kvList)
  while i < l:
    if isinstance(kvList[i], (bool, int)):
      msg += str(kvList[i])
    else:
      msg += kvList[i]
    i += 1
    if i < l:
      val = kvList[i]
      if (val is not None) or (i == l-1):
        msg += u':'
        if (val is not None) and (not isinstance(val, (str, unicode)) or len(val) > 0):
          msg += u' '
          if isinstance(val, (bool, int)):
            msg += str(val)
          else:
            msg += val
        i += 1
        if i < l:
          msg += u', '
      else:
        i += 1
        if i < l:
          msg += u' '
  msg += suffixStr
  if GM_Globals[GM_WINDOWS]:
    return msg
  return msg.encode(GM_Globals[GM_SYS_ENCODING])

def indentMultiLineText(message, n=0):
  return message.replace(u'\n', u'\n{0}'.format(u' '*n)).rstrip()

# Error exits
def setSysExitRC(sysRC):
  GM_Globals[GM_SYSEXITRC] = sysRC

def stderrErrorMsg(message):
  sys.stderr.write(convertUTF8(u'\n{0}{1}\n'.format(ERROR_PREFIX, message)))

def stderrWarningMsg(message):
  sys.stderr.write(convertUTF8(u'\n{0}{1}\n'.format(WARNING_PREFIX, message)))

def systemErrorExit(sysRC, message):
  if message:
    stderrErrorMsg(message)
  sys.exit(sysRC)

def invalidJSONExit(fileName):
  systemErrorExit(INVALID_JSON_RC, MESSAGE_INVALID_JSON.format(fileName))

def noPythonSSLExit():
  systemErrorExit(CERTIFICATE_VALIDATION_UNSUPPORTED_RC, MESSAGE_NO_PYTHON_SSL)

def usageErrorExit(message, extraneous=False):
  if extraneous:
    sys.stderr.write(convertUTF8(u'Command: {0} >>>{1}<<<\n'.format(makeQuotedList(CL_argv[:CL_argvI]),
                                                                    makeQuotedList(CL_argv[CL_argvI:]))))
  elif CL_argvI < CL_argvLen:
    sys.stderr.write(convertUTF8(u'Command: {0} >>>{1}<<< {2}\n'.format(makeQuotedList(CL_argv[:CL_argvI]),
                                                                        makeQuotedList([CL_argv[CL_argvI]]),
                                                                        makeQuotedList(CL_argv[CL_argvI+1:]))))
  else:
    sys.stderr.write(convertUTF8(u'Command: {0} >>><<<\n'.format(makeQuotedList(CL_argv))))
  stderrErrorMsg(message)
  sys.stderr.write(u'Help: Documentation is at {0}\n'.format(GAM_WIKI))
  sys.exit(USAGE_ERROR_RC)

# Invalid CSV ~Header or ~~Header~~
def csvFieldErrorExit(fieldName, fieldNames, backupArg=False, checkForCharset=False):
  if backupArg:
    putArgumentBack()
    if checkForCharset and CL_argv[CL_argvI-1] == u'charset':
      putArgumentBack()
      putArgumentBack()
  usageErrorExit(MESSAGE_HEADER_NOT_FOUND_IN_CSV_HEADERS.format(fieldName, u','.join(fieldNames)))

def unknownArgumentExit():
  putArgumentBack()
  usageErrorExit(ARGUMENT_ERROR_NAMES[ARGUMENT_INVALID][1])

def expectedArgumentExit(problem, argument):
  usageErrorExit(u'{0}: {1} <{2}>'.format(problem, PHRASE_EXPECTED, argument))

def blankArgumentExit(argument):
  expectedArgumentExit(ARGUMENT_ERROR_NAMES[ARGUMENT_BLANK][1], u'{0} {1}'.format(PHRASE_NON_BLANK, argument))

def emptyArgumentExit(argument):
  expectedArgumentExit(ARGUMENT_ERROR_NAMES[ARGUMENT_EMPTY][1], u'{0} {1}'.format(PHRASE_NON_EMPTY, argument))

def invalidArgumentExit(argument):
  expectedArgumentExit(ARGUMENT_ERROR_NAMES[ARGUMENT_INVALID][1], argument)

def missingArgumentExit(argument):
  expectedArgumentExit(ARGUMENT_ERROR_NAMES[ARGUMENT_MISSING][1], argument)

def formatChoiceList(choices):
  if isinstance(choices, dict):
    choiceList = choices.keys()
  else:
    choiceList = choices
  if len(choiceList) <= 5:
    return u'|'.join(choiceList)
  else:
    return u'|'.join(sorted(choiceList))

def invalidChoiceExit(choices):
  expectedArgumentExit(ARGUMENT_ERROR_NAMES[ARGUMENT_INVALID][1], formatChoiceList(choices))

def missingChoiceExit(choices):
  expectedArgumentExit(ARGUMENT_ERROR_NAMES[ARGUMENT_MISSING][1], formatChoiceList(choices))

# Initialize arguments
def initializeArguments(args):
  global CL_argv, CL_argvI, CL_argvLen
  CL_argv = args[:]
  CL_argvI = 1
  CL_argvLen = len(CL_argv)

# Put back last argument
def putArgumentBack():
  global CL_argvI
  CL_argvI -= 1

# Check if argument present
def checkArgumentPresent(choices, required=False):
  global CL_argvI
  if CL_argvI < CL_argvLen:
    choice = CL_argv[CL_argvI].strip().lower()
    if choice:
      if choice in choices:
        CL_argvI += 1
        return choice
    if not required:
      return False
    invalidChoiceExit(choices)
  elif not required:
    return False
  missingChoiceExit(choices)

# Peek to see if argument present, do not advance
def peekArgumentPresent(choices):
  if CL_argvI < CL_argvLen:
    choice = CL_argv[CL_argvI].strip().lower()
    if choice and choice in choices:
      return True
  return False

# Check that there are no extraneous arguments at the end of the command line
def checkForExtraneousArguments():
  if CL_argvI < CL_argvLen:
    usageErrorExit(ARGUMENT_ERROR_NAMES[ARGUMENT_EXTRANEOUS][[0, 1][CL_argvI+1 == CL_argvLen]], extraneous=True)

# Get an argument, downshift, delete underscores
def getArgument():
  global CL_argvI
  if CL_argvI < CL_argvLen:
    argument = CL_argv[CL_argvI].lower()
    if argument:
      CL_argvI += 1
      return argument.replace(u'_', u'')
  missingArgumentExit(OB_ARGUMENT)

def getBoolean():
  global CL_argvI
  if CL_argvI < CL_argvLen:
    boolean = CL_argv[CL_argvI].strip().lower()
    if boolean in TRUE_VALUES:
      CL_argvI += 1
      return True
    if boolean in FALSE_VALUES:
      CL_argvI += 1
      return False
    invalidChoiceExit(TRUE_FALSE)
  missingChoiceExit(TRUE_FALSE)

DEFAULT_CHOICE = u'defaultChoice'
CHOICE_ALIASES = u'choiceAliases'
MAP_CHOICE = u'mapChoice'
NO_DEFAULT = u'NoDefault'

def getChoice(choices, **opts):
  global CL_argvI
  if CL_argvI < CL_argvLen:
    choice = CL_argv[CL_argvI].strip().lower()
    if choice:
      if choice in opts.get(CHOICE_ALIASES, []):
        choice = opts[CHOICE_ALIASES][choice]
      if choice not in choices:
        choice = choice.replace(u'_', u'').replace(u'-', u'')
        if choice in opts.get(CHOICE_ALIASES, []):
          choice = opts[CHOICE_ALIASES][choice]
      if choice in choices:
        CL_argvI += 1
        return choice if not opts.get(MAP_CHOICE, False) else choices[choice]
    if opts.get(DEFAULT_CHOICE, NO_DEFAULT) != NO_DEFAULT:
      return opts[DEFAULT_CHOICE]
    invalidChoiceExit(choices)
  elif opts.get(DEFAULT_CHOICE, NO_DEFAULT) != NO_DEFAULT:
    return opts[DEFAULT_CHOICE]
  missingChoiceExit(choices)

COLORHEX_PATTERN = re.compile(r'#[0-9a-fA-F]{6}')
COLORHEX_FORMAT_REQUIRED = u'#ffffff'

def getColorHexAttribute():
  global CL_argvI
  if CL_argvI < CL_argvLen:
    tg = COLORHEX_PATTERN.match(CL_argv[CL_argvI].strip())
    if tg:
      CL_argvI += 1
      return tg.group(0)
    invalidArgumentExit(COLORHEX_FORMAT_REQUIRED)
  missingArgumentExit(COLORHEX_FORMAT_REQUIRED)

def removeCourseIdScope(courseId):
  if courseId.startswith(u'd:'):
    return courseId[2:]
  return courseId

def addCourseIdScope(courseId):
  if not courseId.isdigit() and courseId[:2] != u'd:':
    return u'd:{0}'.format(courseId)
  return courseId

def getCourseId():
  global CL_argvI
  if CL_argvI < CL_argvLen:
    courseId = CL_argv[CL_argvI]
    if courseId:
      CL_argvI += 1
      return addCourseIdScope(courseId)
  missingArgumentExit(OB_COURSE_ID)

def getCourseAlias():
  global CL_argvI
  if CL_argvI < CL_argvLen:
    courseAlias = CL_argv[CL_argvI]
    if courseAlias:
      CL_argvI += 1
      if courseAlias[:2] != u'd:':
        return u'd:{0}'.format(courseAlias)
      return courseAlias
  missingArgumentExit(OB_COURSE_ALIAS)

UID_PATTERN = re.compile(r'u?id: ?(.*)')

def validateEmailAddressOrUID(emailAddressOrUID):
  cg = UID_PATTERN.match(emailAddressOrUID)
  if cg:
    return cg.group(1)
  return emailAddressOrUID.find(u'@') != 0 and emailAddressOrUID.count(u'@') <= 1

# Normalize user/group email address/uid
# uid:12345abc -> 12345abc
# foo -> foo@domain
# foo@ -> foo@domain
# foo@bar.com -> foo@bar.com
# @domain -> domain
def normalizeEmailAddressOrUID(emailAddressOrUID, noUid=False):
  if not noUid:
    cg = UID_PATTERN.match(emailAddressOrUID)
    if cg:
      return cg.group(1)
  atLoc = emailAddressOrUID.find(u'@')
  if atLoc == 0:
    return emailAddressOrUID[1:].lower()
  if (atLoc == -1) or (atLoc == len(emailAddressOrUID)-1) and GC_Values[GC_DOMAIN]:
    if atLoc == -1:
      emailAddressOrUID = u'{0}@{1}'.format(emailAddressOrUID, GC_Values[GC_DOMAIN])
    else:
      emailAddressOrUID = u'{0}{1}'.format(emailAddressOrUID, GC_Values[GC_DOMAIN])
  return emailAddressOrUID.lower()

# Normalize student/guardian email address/uid
# 12345678 -> 12345678
# - -> -
# Otherwise, same results as normalizeEmailAddressOrUID
def normalizeStudentGuardianEmailAddressOrUID(emailAddressOrUID):
  if emailAddressOrUID.isdigit() or emailAddressOrUID == u'-':
    return emailAddressOrUID
  return normalizeEmailAddressOrUID(emailAddressOrUID)

def getEmailAddress(noUid=False, minLen=1, optional=False):
  global CL_argvI
  if CL_argvI < CL_argvLen:
    emailAddress = CL_argv[CL_argvI].strip().lower()
    if emailAddress:
      cg = UID_PATTERN.match(emailAddress)
      if cg:
        if not noUid:
          if cg.group(1):
            CL_argvI += 1
            return cg.group(1)
        else:
          invalidArgumentExit(u'name@domain')
      else:
        atLoc = emailAddress.find(u'@')
        if atLoc == -1:
          if GC_Values[GC_DOMAIN]:
            emailAddress = u'{0}@{1}'.format(emailAddress, GC_Values[GC_DOMAIN])
          CL_argvI += 1
          return emailAddress
        if atLoc != 0:
          if (atLoc == len(emailAddress)-1) and GC_Values[GC_DOMAIN]:
            emailAddress = u'{0}{1}'.format(emailAddress, GC_Values[GC_DOMAIN])
          CL_argvI += 1
          return emailAddress
        invalidArgumentExit(u'name@domain')
    if optional:
      CL_argvI += 1
      return None
    elif minLen == 0:
      CL_argvI += 1
      return u''
  elif optional:
    return None
  missingArgumentExit([OB_EMAIL_ADDRESS_OR_UID, OB_EMAIL_ADDRESS][noUid])

def getPermissionId():
  global CL_argvI
  if CL_argvI < CL_argvLen:
    emailAddress = CL_argv[CL_argvI].strip().lower()
    if emailAddress:
      if emailAddress[:3] == u'id:':
        CL_argvI += 1
        return (False, CL_argv[CL_argvI-1].strip()[3:])
      atLoc = emailAddress.find(u'@')
      if atLoc == -1:
        if emailAddress == u'anyone':
          CL_argvI += 1
          return (False, emailAddress)
        if emailAddress == u'anyonewithlink':
          CL_argvI += 1
          return (False, u'anyoneWithLink')
        if GC_Values[GC_DOMAIN]:
          emailAddress = u'{0}@{1}'.format(emailAddress, GC_Values[GC_DOMAIN])
        CL_argvI += 1
        return (True, emailAddress)
      if atLoc != 0:
        if (atLoc == len(emailAddress)-1) and GC_Values[GC_DOMAIN]:
          emailAddress = u'{0}{1}'.format(emailAddress, GC_Values[GC_DOMAIN])
        CL_argvI += 1
        return (True, emailAddress)
      invalidArgumentExit(u'name@domain')
  missingArgumentExit(OB_PERMISSION_ID)

# Products/SKUs
#
GOOGLE_APPS_PRODUCT = u'Google-Apps'
GOOGLE_COORDINATE_PRODUCT = u'Google-Coordinate'
GOOGLE_DRIVE_STORAGE_PRODUCT = u'Google-Drive-storage'
GOOGLE_VAULT_PRODUCT = u'Google-Vault'

GOOGLE_PRODUCTS = [
  GOOGLE_APPS_PRODUCT,
  GOOGLE_COORDINATE_PRODUCT,
  GOOGLE_DRIVE_STORAGE_PRODUCT,
  GOOGLE_VAULT_PRODUCT,
  ]

GOOGLE_APPS_FOR_BUSINESS_SKU = GOOGLE_APPS_PRODUCT+u'-For-Business'
GOOGLE_APPS_FOR_POSTINI_SKU = GOOGLE_APPS_PRODUCT+u'-For-Postini'
GOOGLE_APPS_LITE_SKU = GOOGLE_APPS_PRODUCT+u'-Lite'
GOOGLE_APPS_UNLIMITED_SKU = GOOGLE_APPS_PRODUCT+u'-Unlimited'
GOOGLE_COORDINATE_SKU = GOOGLE_COORDINATE_PRODUCT
GOOGLE_VAULT_SKU = GOOGLE_VAULT_PRODUCT
GOOGLE_VAULT_FORMER_EMPLOYEE_SKU = GOOGLE_VAULT_PRODUCT+u'-Former-Employee'
GOOGLE_DRIVE_STORAGE_20GB_SKU = GOOGLE_DRIVE_STORAGE_PRODUCT+u'-20GB'
GOOGLE_DRIVE_STORAGE_50GB_SKU = GOOGLE_DRIVE_STORAGE_PRODUCT+u'-50GB'
GOOGLE_DRIVE_STORAGE_200GB_SKU = GOOGLE_DRIVE_STORAGE_PRODUCT+u'-200GB'
GOOGLE_DRIVE_STORAGE_400GB_SKU = GOOGLE_DRIVE_STORAGE_PRODUCT+u'-400GB'
GOOGLE_DRIVE_STORAGE_1TB_SKU = GOOGLE_DRIVE_STORAGE_PRODUCT+u'-1TB'
GOOGLE_DRIVE_STORAGE_2TB_SKU = GOOGLE_DRIVE_STORAGE_PRODUCT+u'-2TB'
GOOGLE_DRIVE_STORAGE_4TB_SKU = GOOGLE_DRIVE_STORAGE_PRODUCT+u'-4TB'
GOOGLE_DRIVE_STORAGE_8TB_SKU = GOOGLE_DRIVE_STORAGE_PRODUCT+u'-8TB'
GOOGLE_DRIVE_STORAGE_16TB_SKU = GOOGLE_DRIVE_STORAGE_PRODUCT+u'-16TB'

GOOGLE_USER_SKUS = {
  GOOGLE_APPS_FOR_BUSINESS_SKU: GOOGLE_APPS_PRODUCT,
  GOOGLE_APPS_FOR_POSTINI_SKU: GOOGLE_APPS_PRODUCT,
  GOOGLE_APPS_LITE_SKU: GOOGLE_APPS_PRODUCT,
  GOOGLE_APPS_UNLIMITED_SKU: GOOGLE_APPS_PRODUCT,
  GOOGLE_VAULT_SKU: GOOGLE_VAULT_PRODUCT,
  GOOGLE_VAULT_FORMER_EMPLOYEE_SKU: GOOGLE_VAULT_PRODUCT,
  }
GOOGLE_SKUS = {
  GOOGLE_APPS_FOR_BUSINESS_SKU: GOOGLE_APPS_PRODUCT,
  GOOGLE_APPS_FOR_POSTINI_SKU: GOOGLE_APPS_PRODUCT,
  GOOGLE_APPS_LITE_SKU: GOOGLE_APPS_PRODUCT,
  GOOGLE_APPS_UNLIMITED_SKU: GOOGLE_APPS_PRODUCT,
  GOOGLE_COORDINATE_SKU: GOOGLE_COORDINATE_PRODUCT,
  GOOGLE_VAULT_SKU: GOOGLE_VAULT_PRODUCT,
  GOOGLE_VAULT_FORMER_EMPLOYEE_SKU: GOOGLE_VAULT_PRODUCT,
  GOOGLE_DRIVE_STORAGE_20GB_SKU: GOOGLE_DRIVE_STORAGE_PRODUCT,
  GOOGLE_DRIVE_STORAGE_50GB_SKU: GOOGLE_DRIVE_STORAGE_PRODUCT,
  GOOGLE_DRIVE_STORAGE_200GB_SKU: GOOGLE_DRIVE_STORAGE_PRODUCT,
  GOOGLE_DRIVE_STORAGE_400GB_SKU: GOOGLE_DRIVE_STORAGE_PRODUCT,
  GOOGLE_DRIVE_STORAGE_1TB_SKU: GOOGLE_DRIVE_STORAGE_PRODUCT,
  GOOGLE_DRIVE_STORAGE_2TB_SKU: GOOGLE_DRIVE_STORAGE_PRODUCT,
  GOOGLE_DRIVE_STORAGE_4TB_SKU: GOOGLE_DRIVE_STORAGE_PRODUCT,
  GOOGLE_DRIVE_STORAGE_8TB_SKU: GOOGLE_DRIVE_STORAGE_PRODUCT,
  GOOGLE_DRIVE_STORAGE_16TB_SKU: GOOGLE_DRIVE_STORAGE_PRODUCT,
  }

GOOGLE_SKU_CHOICES_MAP = {
  u'apps': GOOGLE_APPS_FOR_BUSINESS_SKU,
  u'gafb': GOOGLE_APPS_FOR_BUSINESS_SKU,
  u'gafw': GOOGLE_APPS_FOR_BUSINESS_SKU,
  u'gsbasic': GOOGLE_APPS_FOR_BUSINESS_SKU,
  u'gams': GOOGLE_APPS_FOR_POSTINI_SKU,
  u'lite': GOOGLE_APPS_LITE_SKU,
  u'gau': GOOGLE_APPS_UNLIMITED_SKU,
  u'unlimited': GOOGLE_APPS_UNLIMITED_SKU,
  u'd4w': GOOGLE_APPS_UNLIMITED_SKU,
  u'dfw': GOOGLE_APPS_UNLIMITED_SKU,
  u'gsbusiness': GOOGLE_APPS_UNLIMITED_SKU,
  u'coordinate': GOOGLE_COORDINATE_SKU,
  u'vault': GOOGLE_VAULT_SKU,
  u'vfe': GOOGLE_VAULT_FORMER_EMPLOYEE_SKU,
  u'drive-20gb': GOOGLE_DRIVE_STORAGE_20GB_SKU,
  u'drive20gb': GOOGLE_DRIVE_STORAGE_20GB_SKU,
  u'20gb': GOOGLE_DRIVE_STORAGE_20GB_SKU,
  u'drive-50gb': GOOGLE_DRIVE_STORAGE_50GB_SKU,
  u'drive50gb': GOOGLE_DRIVE_STORAGE_50GB_SKU,
  u'50gb': GOOGLE_DRIVE_STORAGE_50GB_SKU,
  u'drive-200gb': GOOGLE_DRIVE_STORAGE_200GB_SKU,
  u'drive200gb': GOOGLE_DRIVE_STORAGE_200GB_SKU,
  u'200gb': GOOGLE_DRIVE_STORAGE_200GB_SKU,
  u'drive-400gb': GOOGLE_DRIVE_STORAGE_400GB_SKU,
  u'drive400gb': GOOGLE_DRIVE_STORAGE_400GB_SKU,
  u'400gb': GOOGLE_DRIVE_STORAGE_400GB_SKU,
  u'drive-1tb': GOOGLE_DRIVE_STORAGE_1TB_SKU,
  u'drive1tb': GOOGLE_DRIVE_STORAGE_1TB_SKU,
  u'1tb': GOOGLE_DRIVE_STORAGE_1TB_SKU,
  u'drive-2tb': GOOGLE_DRIVE_STORAGE_2TB_SKU,
  u'drive2tb': GOOGLE_DRIVE_STORAGE_2TB_SKU,
  u'2tb': GOOGLE_DRIVE_STORAGE_2TB_SKU,
  u'drive-4tb': GOOGLE_DRIVE_STORAGE_4TB_SKU,
  u'drive4tb': GOOGLE_DRIVE_STORAGE_4TB_SKU,
  u'4tb': GOOGLE_DRIVE_STORAGE_4TB_SKU,
  u'drive-8tb': GOOGLE_DRIVE_STORAGE_8TB_SKU,
  u'drive8tb': GOOGLE_DRIVE_STORAGE_8TB_SKU,
  u'8tb': GOOGLE_DRIVE_STORAGE_8TB_SKU,
  u'drive-16tb': GOOGLE_DRIVE_STORAGE_16TB_SKU,
  u'drive16tb': GOOGLE_DRIVE_STORAGE_16TB_SKU,
  u'16tb': GOOGLE_DRIVE_STORAGE_16TB_SKU,
  }

def getGoogleProductListMap():
  global CL_argvI
  if CL_argvI < CL_argvLen:
    productsOK = True
    products = CL_argv[CL_argvI].replace(u',', u' ').split()
    productsMapped = []
    for product in products:
      if product in GOOGLE_PRODUCTS:
        productsMapped.append(product)
      else:
        product = product.lower()
        if product in GOOGLE_SKU_CHOICES_MAP:
          productsMapped.append(GOOGLE_SKUS[GOOGLE_SKU_CHOICES_MAP[product]])
        else:
          productsOK = False
    if productsOK:
      CL_argvI += 1
      return productsMapped
    invalidChoiceExit(GOOGLE_SKU_CHOICES_MAP)
  missingArgumentExit(OB_PRODUCT_ID_LIST)

def getGoogleSKUMap(matchProduct=None):
  global CL_argvI
  if CL_argvI < CL_argvLen:
    skuOK = True
    sku = CL_argv[CL_argvI].strip()
    if sku:
      if sku not in GOOGLE_SKUS:
        sku = sku.lower()
        if sku in GOOGLE_SKU_CHOICES_MAP:
          sku = GOOGLE_SKU_CHOICES_MAP[sku]
        else:
          skuOK = False
      if skuOK:
        if (not matchProduct) or (GOOGLE_SKUS[sku] == matchProduct):
          CL_argvI += 1
          return sku
      invalidChoiceExit(GOOGLE_SKU_CHOICES_MAP)
  missingArgumentExit(OB_SKU_ID)

def getGoogleSKUListMap():
  global CL_argvI
  if CL_argvI < CL_argvLen:
    skusOK = True
    skus = CL_argv[CL_argvI].replace(u',', u' ').split()
    skusMapped = []
    for sku in skus:
      if sku in GOOGLE_SKUS:
        skusMapped.append(GOOGLE_SKU_CHOICES_MAP[sku])
      else:
        sku = sku.lower()
        if sku in GOOGLE_SKU_CHOICES_MAP:
          skusMapped.append(GOOGLE_SKU_CHOICES_MAP[sku])
        else:
          skusOK = False
    if skusOK:
      CL_argvI += 1
      return skusMapped
    invalidChoiceExit(GOOGLE_SKU_CHOICES_MAP)
  missingArgumentExit(OB_SKU_ID_LIST)

def integerLimits(minVal, maxVal, item=u'integer'):
  if (minVal is not None) and (maxVal is not None):
    return u'{0} {1}<=x<={2}'.format(item, minVal, maxVal)
  if minVal is not None:
    return u'{0} x>={1}'.format(item, minVal)
  if maxVal is not None:
    return u'{0} x<={1}'.format(item, maxVal)
  return u'{0} x'.format(item)

def getInteger(minVal=None, maxVal=None):
  global CL_argvI
  if CL_argvI < CL_argvLen:
    try:
      number = int(CL_argv[CL_argvI].strip())
      if ((minVal is None) or (number >= minVal)) and ((maxVal is None) or (number <= maxVal)):
        CL_argvI += 1
        return number
    except ValueError:
      pass
    invalidArgumentExit(integerLimits(minVal, maxVal))
  missingArgumentExit(integerLimits(minVal, maxVal))

def orgUnitPathQuery(path):
  return u"orgUnitPath='{0}'".format(path.replace(u"'", u"\'"))

def makeOrgUnitPathAbsolute(path):
  if path == u'/':
    return path
  if path.startswith(u'/'):
    return path.rstrip(u'/')
  if path.startswith(u'id:'):
    return path
  if path.startswith(u'uid:'):
    return path[1:]
  return u'/'+path.rstrip(u'/')

def makeOrgUnitPathRelative(path):
  if path == u'/':
    return path
  if path.startswith(u'/'):
    return path[1:].rstrip(u'/')
  if path.startswith(u'id:'):
    return path
  if path.startswith(u'uid:'):
    return path[1:]
  return path.rstrip(u'/')

def getOrgUnitPath(absolutePath=True):
  global CL_argvI
  if CL_argvI < CL_argvLen:
    path = CL_argv[CL_argvI].strip()
    if path:
      CL_argvI += 1
      if absolutePath:
        return makeOrgUnitPathAbsolute(path)
      return makeOrgUnitPathRelative(path)
  missingArgumentExit(OB_ORGUNIT_PATH)

def getREPattern():
  global CL_argvI
  if CL_argvI < CL_argvLen:
    patstr = CL_argv[CL_argvI]
    if patstr:
      try:
        pattern = re.compile(patstr)
        CL_argvI += 1
        return pattern
      except re.error as e:
        usageErrorExit(u'{0} {1}: {2}'.format(OB_RE_PATTERN, PHRASE_ERROR, e))
  missingArgumentExit(OB_RE_PATTERN)

def getString(item, checkBlank=False, optional=False, minLen=1, maxLen=None):
  global CL_argvI
  if CL_argvI < CL_argvLen:
    argstr = CL_argv[CL_argvI]
    if argstr:
      if checkBlank:
        if argstr.isspace():
          blankArgumentExit(item)
      if (len(argstr) >= minLen) and ((maxLen is None) or (len(argstr) <= maxLen)):
        CL_argvI += 1
        return argstr
      invalidArgumentExit(u'{0} for {1}'.format(integerLimits(minLen, maxLen, PHRASE_STRING_LENGTH), item))
    if optional or (minLen == 0):
      CL_argvI += 1
      return u''
    emptyArgumentExit(item)
  elif optional:
    return u''
  missingArgumentExit(item)

def getStringReturnInList(item):
  argstr = getString(item, minLen=0)
  if argstr:
    return [argstr]
  return []

YYYYMMDD_FORMAT = u'%Y-%m-%d'
YYYYMMDD_FORMAT_REQUIRED = u'yyyy-mm-dd'

def getYYYYMMDD(minLen=1, returnTimeStamp=False):
  global CL_argvI
  if CL_argvI < CL_argvLen:
    argstr = CL_argv[CL_argvI].strip()
    if argstr:
      try:
        timeStamp = time.mktime(datetime.datetime.strptime(argstr, YYYYMMDD_FORMAT).timetuple())*1000
        CL_argvI += 1
        if not returnTimeStamp:
          return argstr
        return timeStamp
      except ValueError:
        invalidArgumentExit(YYYYMMDD_FORMAT_REQUIRED)
    elif minLen == 0:
      CL_argvI += 1
      return u''
  missingArgumentExit(YYYYMMDD_FORMAT_REQUIRED)

YYYYMMDD_HHMM_FORMAT = u'%Y-%m-%d %H:%M'
YYYYMMDD_HHMM_FORMAT_REQUIRED = u'yyyy-mm-dd hh:mm'

def getYYYYMMDD_HHMM():
  global CL_argvI
  if CL_argvI < CL_argvLen:
    argstr = CL_argv[CL_argvI].strip().upper().replace(u'T', u' ')
    if argstr:
      try:
        datetime.datetime.strptime(argstr, YYYYMMDD_HHMM_FORMAT)
        CL_argvI += 1
        return argstr
      except ValueError:
        invalidArgumentExit(YYYYMMDD_HHMM_FORMAT_REQUIRED)
  missingArgumentExit(YYYYMMDD_HHMM_FORMAT_REQUIRED)

YYYYMMDDTHHMMSS_FORMAT_REQUIRED = u'yyyy-mm-ddThh:mm:ss[.fff]Z|+hh:mm|-hh:mm'

def getFullTime(returnDateTime=False):
  global CL_argvI
  if CL_argvI < CL_argvLen:
    argstr = CL_argv[CL_argvI].strip().upper().replace(u' ', u'T')
    if argstr:
      try:
        fullDateTime, tz = iso8601.parse_date(argstr)
        CL_argvI += 1
        if not returnDateTime:
          return argstr.replace(u' ', u'T')
        return (fullDateTime, tz, argstr.replace(u' ', u'T'))
      except iso8601.ParseError:
        pass
      invalidArgumentExit(YYYYMMDDTHHMMSS_FORMAT_REQUIRED)
  missingArgumentExit(YYYYMMDDTHHMMSS_FORMAT_REQUIRED)

EVENT_TIME_FORMAT_REQUIRED = u'allday yyyy-mm-dd | yyyy-mm-ddThh:mm:ss[.fff]Z|+hh:mm|-hh:mm'

def getEventTime():
  global CL_argvI
  if CL_argvI < CL_argvLen:
    if CL_argv[CL_argvI].strip().lower() == u'allday':
      CL_argvI += 1
      return {u'date': getYYYYMMDD()}
    return {u'dateTime': getFullTime()}
  missingArgumentExit(EVENT_TIME_FORMAT_REQUIRED)

AGE_TIME_PATTERN = re.compile(r'^(\d+)([mhd]?)$')
AGE_TIME_FORMAT_REQUIRED = u'<Number>[m|h|d]'

def getAgeTime():
  global CL_argvI
  if CL_argvI < CL_argvLen:
    tg = AGE_TIME_PATTERN.match(CL_argv[CL_argvI].strip().lower())
    if tg:
      tgg = tg.groups(u'0')
      age = int(tgg[0])
      age_unit = tgg[1]
      now = int(time.time())
      if age_unit == u'm':
        age = now-(age*SECONDS_PER_MINUTE)
      elif age_unit == u'h':
        age = now-(age*SECONDS_PER_HOUR)
      else: # age_unit == u'd':
        age = now-(age*SECONDS_PER_DAY)
      CL_argvI += 1
      return age*1000
    invalidArgumentExit(AGE_TIME_FORMAT_REQUIRED)
  missingArgumentExit(AGE_TIME_FORMAT_REQUIRED)

CALENDAR_REMINDER_METHODS = [u'email', u'sms', u'popup',]

def getCalendarReminder(allowClearNone=False):
  methods = CALENDAR_REMINDER_METHODS
  if allowClearNone:
    methods += CLEAR_NONE_ARGUMENT
  if CL_argvI < CL_argvLen:
    method = CL_argv[CL_argvI].strip()
    if not method.isdigit():
      method = getChoice(methods)
      minutes = getInteger(minVal=0, maxVal=40320)
    else:
      minutes = getInteger(minVal=0, maxVal=40320)
      method = getChoice(methods)
    return {u'method': method, u'minutes': minutes}
  missingChoiceExit(methods)

def getCharSet():
  if not checkArgumentPresent([u'charset',]):
    return GC_Values.get(GC_CHARSET, GM_Globals[GM_SYS_ENCODING])
  return getString(OB_CHAR_SET)

def getDelimiter():
  if checkArgumentPresent([u'delimiter',]):
    return getString(OB_STRING)
  return None

def getMatchFields(fieldNames):
  matchFields = {}
  while checkArgumentPresent([u'matchfield',]):
    matchField = getString(OB_FIELD_NAME).strip(u'~')
    if (not matchField) or (matchField not in fieldNames):
      csvFieldErrorExit(matchField, fieldNames, backupArg=True)
    matchFields[matchField] = getREPattern()
  return matchFields

def checkMatchFields(row, matchFields):
  for matchField, matchPattern in matchFields.items():
    if (matchField not in row) or not matchPattern.search(row[matchField]):
      return False
  return True

MAX_MESSAGE_BYTES_PATTERN = re.compile(r'^(\d+)([mkb]?)$')
MAX_MESSAGE_BYTES_FORMAT_REQUIRED = u'<Number>[m|k|b]'

def getMaxMessageBytes():
  global CL_argvI
  if CL_argvI < CL_argvLen:
    tg = MAX_MESSAGE_BYTES_PATTERN.match(CL_argv[CL_argvI].strip().lower())
    if tg:
      tgg = tg.groups(u'0')
      mmb = int(tgg[0])
      mmb_unit = tgg[1]
      if mmb_unit == u'm':
        mmb *= ONE_MEGA_BYTES
      elif mmb_unit == u'k':
        mmb *= ONE_KILO_BYTES
      CL_argvI += 1
      return mmb
    invalidArgumentExit(MAX_MESSAGE_BYTES_FORMAT_REQUIRED)
  missingArgumentExit(MAX_MESSAGE_BYTES_FORMAT_REQUIRED)

# Get domain from email address
def getEmailAddressDomain(emailAddress):
  atLoc = emailAddress.find(u'@')
  if atLoc == -1:
    return GC_Values[GC_DOMAIN].lower()
  return emailAddress[atLoc+1:].lower()

# Get user name from email address
def getEmailAddressUsername(emailAddress):
  atLoc = emailAddress.find(u'@')
  if atLoc == -1:
    return emailAddress.lower()
  return emailAddress[:atLoc].lower()

# Split email address unto user and domain
def splitEmailAddress(emailAddress):
  atLoc = emailAddress.find(u'@')
  if atLoc == -1:
    return (emailAddress.lower(), GC_Values[GC_DOMAIN].lower())
  return (emailAddress[:atLoc].lower(), emailAddress[atLoc+1:].lower())

def formatFileSize(fileSize):
  if fileSize == 0:
    return u'0kb'
  if fileSize < ONE_KILO_BYTES:
    return u'1kb'
  if fileSize < ONE_MEGA_BYTES:
    return u'{0}kb'.format(fileSize / ONE_KILO_BYTES)
  if fileSize < ONE_GIGA_BYTES:
    return u'{0}mb'.format(fileSize / ONE_MEGA_BYTES)
  return u'{0}gb'.format(fileSize / ONE_GIGA_BYTES)

def formatMaxMessageBytes(maxMessageBytes):
  if maxMessageBytes < ONE_KILO_BYTES:
    return maxMessageBytes
  if maxMessageBytes < ONE_MEGA_BYTES:
    return u'{0}K'.format(maxMessageBytes / ONE_KILO_BYTES)
  return u'{0}M'.format(maxMessageBytes / ONE_MEGA_BYTES)

def formatMilliSeconds(millis):
  seconds, millis = divmod(millis, 1000)
  minutes, seconds = divmod(seconds, 60)
  hours, minutes = divmod(minutes, 60)
  return u'%02d:%02d:%02d' % (hours, minutes, seconds)

def currentCount(i, count):
  return u' ({0}/{1})'.format(i, count)

def currentCountNL(i, count):
  return u' ({0}/{1})\n'.format(i, count)

def formatHTTPError(http_status, reason, message):
  return u'{0}: {1} - {2}'.format(http_status, reason, message)

def entityServiceNotApplicableWarning(entityType, entityName, i, count):
  sys.stderr.write(u'{0}: {1}, Service not applicable/Does not exist{2}'.format(entityType, entityName, currentCountNL(i, count)))

def entityDoesNotExistWarning(entityType, entityName, i, count):
  sys.stderr.write(u'{0}: {1}, Does not exist{2}'.format(entityType, entityName, currentCountNL(i, count)))

def entityUnknownWarning(entityType, entityName, i, count):
  domain = getEmailAddressDomain(entityName)
  if (domain == GC_Values[GC_DOMAIN]) or (domain.endswith(u'google.com')):
    entityDoesNotExistWarning(entityType, entityName, i, count)
  else:
    entityServiceNotApplicableWarning(entityType, entityName, i, count)

def printLine(message):
  sys.stdout.write(message+u'\n')

def printBlankLine():
  sys.stdout.write(u'\n')

def printKeyValueList(spacing, kvList):
  sys.stdout.write(formatKeyValueList(spacing, kvList, u'\n'))

def printKeyValueListWithCount(spacing, kvList, i, count):
  sys.stdout.write(formatKeyValueList(spacing, kvList, currentCountNL(i, count)))

def printKeyValueDict(spacing, kvDict):
  for key, value in kvDict.iteritems():
    sys.stdout.write(formatKeyValueList(spacing, [key, value], u'\n'))

def printJSONKey(spacing, key):
  sys.stdout.write(formatKeyValueList(spacing, [key, u''], u''))

def printJSONValue(value):
  sys.stdout.write(formatKeyValueList(u' ', [value], u'\n'))

# Open a file
def openFile(filename, mode=u'rU'):
  try:
    if filename != u'-':
      return open(os.path.expanduser(filename), mode)
    if mode.startswith(u'r'):
      return StringIO.StringIO(unicode(sys.stdin.read()))
    return sys.stdout
  except IOError as e:
    systemErrorExit(FILE_ERROR_RC, e)

# Close a file
def closeFile(f):
  try:
    f.close()
    return True
  except IOError as e:
    stderrErrorMsg(e)
    setSysExitRC(FILE_ERROR_RC)
    return False

# Read a file
def readFile(filename, mode=u'rb', continueOnError=False, displayError=True, encoding=None):
  try:
    if filename != u'-':
      if not encoding:
        with open(os.path.expanduser(filename), mode) as f:
          return f.read()
      with codecs.open(os.path.expanduser(filename), mode, encoding) as f:
        content = f.read()
# codecs does not strip UTF-8 BOM (ef:bb:bf) so we must
        if not content.startswith(codecs.BOM_UTF8):
          return content
        return content[3:]
    return unicode(sys.stdin.read())
  except IOError as e:
    if continueOnError:
      if displayError:
        stderrWarningMsg(e)
        setSysExitRC(FILE_ERROR_RC)
      return None
    systemErrorExit(FILE_ERROR_RC, e)
  except (LookupError, UnicodeDecodeError, UnicodeError) as e:
    putArgumentBack()
    usageErrorExit(e)

# Write a file
def writeFile(filename, data, mode=u'wb', continueOnError=False, displayError=True):
  try:
    with open(os.path.expanduser(filename), mode) as f:
      f.write(data)
    return True
  except IOError as e:
    if continueOnError:
      if displayError:
        stderrErrorMsg(e)
      setSysExitRC(FILE_ERROR_RC)
      return False
    systemErrorExit(FILE_ERROR_RC, e)
#
class UTF8Recoder(object):
  """
  Iterator that reads an encoded stream and reencodes the input to UTF-8
  """
  def __init__(self, f, encoding):
    self.reader = codecs.getreader(encoding)(f)

  def __iter__(self):
    return self

  def next(self):
    return self.reader.next().encode(u'utf-8')

class UnicodeDictReader(object):
  """
  A CSV reader which will iterate over lines in the CSV file "f",
  which is encoded in the given encoding.
  """

  def __init__(self, f, dialect=csv.excel, encoding=u'utf-8', fieldnames=None, **kwds):
    self.encoding = encoding
    try:
      self.reader = csv.reader(UTF8Recoder(f, encoding) if self.encoding != u'utf-8' else f, dialect=dialect, **kwds)
      if not fieldnames:
        self.fieldnames = self.reader.next()
        if len(self.fieldnames) > 0 and self.fieldnames[0].startswith(codecs.BOM_UTF8):
          self.fieldnames[0] = self.fieldnames[0].replace(codecs.BOM_UTF8, u'', 1)
      else:
        self.fieldnames = fieldnames
    except (csv.Error, StopIteration):
      self.fieldnames = []
    except LookupError as e:
      putArgumentBack()
      usageErrorExit(e)
    self.numfields = len(self.fieldnames)

  def __iter__(self):
    return self

  def next(self):
    row = self.reader.next()
    l = len(row)
    if l < self.numfields:
      row += ['']*(self.numfields-l) # Must be '', not u''
    return dict((self.fieldnames[x], unicode(row[x], u'utf-8')) for x in range(self.numfields))

# Open a CSV file, get optional arguments [charset <String>] [columndelimiter <String>] [fields <FieldNameList>]
def openCSVFileReader(filename):
  encoding = getCharSet()
  if checkArgumentPresent(COLUMN_DELIMITER_ARGUMENT):
    delimiter = getString(OB_STRING, minLen=1, maxLen=1)
  else:
    delimiter = GC_Values.get(GC_CSV_INPUT_COLUMN_DELIMITER, GC_Defaults[GC_CSV_INPUT_COLUMN_DELIMITER])
  if checkArgumentPresent([u'fields',]):
    fieldnames = shlexSplitList(getString(OB_FIELD_NAME_LIST))
  else:
    fieldnames = None
  f = openFile(filename)
  csvFile = UnicodeDictReader(f, encoding=encoding, fieldnames=fieldnames, delimiter=str(delimiter))
  return (f, csvFile)

# Set global variables
# Check for GAM updates based on status of noupdatecheck.txt
#
def SetGlobalVariables():

  def _getDefault(itemName, itemEntry):
    if GC_VAR_SIGFILE in itemEntry:
      GC_Defaults[itemName] = itemEntry[GC_VAR_SFFT][os.path.isfile(os.path.join(GC_Defaults[GC_CONFIG_DIR], itemEntry[GC_VAR_SIGFILE]))]
    else:
      value = os.environ.get(itemEntry[GC_VAR_ENVVAR], GC_Defaults[itemName])
      if itemEntry[GC_VAR_TYPE] == GC_TYPE_INTEGER:
        try:
          number = int(value)
          minVal, maxVal = itemEntry[GC_VAR_LIMITS]
          if (minVal is not None) and (number < minVal):
            number = minVal
          elif (maxVal is not None) and (number > maxVal):
            number = maxVal
        except ValueError:
          number = GC_Defaults[itemName]
        value = number
      GC_Defaults[itemName] = value

  def _getCfgDirectory(itemName):
    dirPath = os.path.expanduser(GC_Defaults[itemName])
    if (not dirPath) or (not os.path.isabs(dirPath)):
      dirPath = os.path.join(GM_Globals[GM_GAM_PATH], dirPath)
    return dirPath

  def _getCfgFile(itemName, GC_Table):
    value = os.path.expanduser(GC_Defaults[itemName])
    if not os.path.isabs(value):
      value = os.path.expanduser(os.path.join(GC_Table[GC_CONFIG_DIR], value))
    return value

  def _verifyValues():
    print u'Gam: Variables'
    for itemName in sorted(GC_VAR_INFO):
      cfgValue = GC_Defaults[itemName]
      if GC_VAR_INFO[itemName][GC_VAR_TYPE] == GC_TYPE_FILE:
        expdValue = _getCfgFile(itemName, GC_Defaults)
        if cfgValue != expdValue:
          cfgValue = u'{0} ; {1}'.format(cfgValue, expdValue)
      elif GC_VAR_INFO[itemName][GC_VAR_TYPE] == GC_TYPE_DIRECTORY:
        expdValue = _getCfgDirectory(itemName)
        if cfgValue != expdValue:
          cfgValue = u'{0} ; {1}'.format(cfgValue, expdValue)
      print u'  {0} = {1}'.format(itemName, cfgValue)

# Read environment variables/signal files
  GC_Defaults[GC_CONFIG_DIR] = GM_Globals[GM_GAM_PATH]
  GC_Defaults[GC_CACHE_DIR] = os.path.join(GM_Globals[GM_GAM_PATH], u'gamcache')
  GC_Defaults[GC_DRIVE_DIR] = GM_Globals[GM_GAM_PATH]
  for itemName, itemEntry in GC_VAR_INFO.items():
    if itemEntry[GC_VAR_TYPE] == GC_TYPE_DIRECTORY:
      _getDefault(itemName, itemEntry)
  for itemName, itemEntry in GC_VAR_INFO.items():
    if itemEntry[GC_VAR_TYPE] != GC_TYPE_DIRECTORY:
      _getDefault(itemName, itemEntry)
# config [<VariableName> <Value>]* [verify]
  if checkArgumentPresent([u'config',]):
    while CL_argvI < CL_argvLen:
      if checkArgumentPresent([u'verify',]):
        _verifyValues()
      else:
        itemName = getChoice(GC_VAR_INFO, defaultChoice=None)
        if itemName is None:
          break
        if GC_VAR_INFO[itemName][GC_VAR_TYPE] == GC_TYPE_BOOLEAN:
          value = getBoolean()
        elif GC_VAR_INFO[itemName][GC_VAR_TYPE] == GC_TYPE_INTEGER:
          minVal, maxVal = GC_VAR_INFO[itemName][GC_VAR_LIMITS]
          value = getInteger(minVal=minVal, maxVal=maxVal)
        else:
          value = getString(OB_STRING)
        GC_Defaults[itemName] = value
# Assign global variables, directories first as other variables depend on them
  for itemName in GC_VAR_INFO:
    if GC_VAR_INFO[itemName][GC_VAR_TYPE] == GC_TYPE_DIRECTORY:
      GC_Values[itemName] = _getCfgDirectory(itemName)
  for itemName in GC_VAR_INFO:
    varType = GC_VAR_INFO[itemName][GC_VAR_TYPE]
    if varType == GC_TYPE_FILE:
      GC_Values[itemName] = _getCfgFile(itemName, GC_Values)
    elif varType != GC_TYPE_DIRECTORY:
      GC_Values[itemName] = GC_Defaults[itemName]
  GM_Globals[GM_LAST_UPDATE_CHECK_TXT] = os.path.join(GC_Values[GC_CONFIG_DIR], FN_LAST_UPDATE_CHECK_TXT)
  if not GC_Values[GC_NO_UPDATE_CHECK]:
    doGAMCheckForUpdates()
# Globals derived from config file values
  GM_Globals[GM_OAUTH2SERVICE_JSON_DATA] = None
  GM_Globals[GM_OAUTH2SERVICE_ACCOUNT_CLIENT_ID] = None
  GM_Globals[GM_EXTRA_ARGS_LIST] = [(u'prettyPrint', GC_Values[GC_DEBUG_LEVEL] > 0)]
  httplib2.debuglevel = GC_Values[GC_DEBUG_LEVEL]
  if os.path.isfile(GC_Values[GC_EXTRA_ARGS]):
    ea_config = ConfigParser.ConfigParser()
    ea_config.optionxform = str
    ea_config.read(GC_Values[GC_EXTRA_ARGS])
    GM_Globals[GM_EXTRA_ARGS_LIST].extend(ea_config.items(u'extra-args'))
  if GC_Values[GC_NO_CACHE]:
    GM_Globals[GM_CACHE_DIR] = None
# If there are more arguments on the command line, return True
  return (CL_argvI == 1) or (CL_argvI < CL_argvLen)

def doGAMCheckForUpdates(forceCheck=False):
  import urllib2
  import calendar

  current_version = __version__
  now_time = calendar.timegm(time.gmtime())
  if forceCheck:
    check_url = GAM_ALL_RELEASES # includes pre-releases
  else:
    last_check_time_str = readFile(GM_Globals[GM_LAST_UPDATE_CHECK_TXT], continueOnError=True, displayError=False)
    last_check_time = int(last_check_time_str) if last_check_time_str and last_check_time_str.isdigit() else 0
    if last_check_time > now_time-604800:
      return
    check_url = GAM_LATEST_RELEASE # latest full release
  headers = {u'Accept': u'application/vnd.github.v3.text+json'}
  request = urllib2.Request(url=check_url, headers=headers)
  try:
    c = urllib2.urlopen(request)
    try:
      release_data = json.loads(c.read())
    except ValueError:
      return
    if isinstance(release_data, list):
      release_data = release_data[0] # only care about latest release
    latest_version = release_data[u'tag_name']
    if latest_version[0].lower() == u'v':
      latest_version = latest_version[1:]
    if forceCheck or (latest_version > current_version):
      print u'Version Check:\n  Current: {0}\n   Latest: {1}'.format(current_version, latest_version)
    if latest_version <= current_version:
      writeFile(GM_Globals[GM_LAST_UPDATE_CHECK_TXT], str(now_time), continueOnError=True, displayError=forceCheck)
      return
    announcement = release_data.get(u'body_text', u'No details about this release')
    sys.stderr.write(u'\nGAM %s release notes:\n\n' % latest_version)
    sys.stderr.write(announcement)
    try:
      printLine(MESSAGE_HIT_CONTROL_C_TO_UPDATE)
      time.sleep(15)
    except KeyboardInterrupt:
      import webbrowser
      webbrowser.open(release_data[u'html_url'])
      printLine(MESSAGE_GAM_EXITING_FOR_UPDATE)
      sys.exit(0)
    writeFile(GM_Globals[GM_LAST_UPDATE_CHECK_TXT], str(now_time), continueOnError=True, displayError=forceCheck)
    return
  except (urllib2.HTTPError, urllib2.URLError):
    return

def handleOAuthTokenError(e, soft_errors):
  if e.message in OAUTH2_TOKEN_ERRORS:
    if soft_errors:
      return None
    if not GM_Globals[GM_CURRENT_API_USER]:
      stderrErrorMsg(MESSAGE_API_ACCESS_DENIED.format(GM_Globals[GM_OAUTH2SERVICE_ACCOUNT_CLIENT_ID],
                                                      u','.join(GM_Globals[GM_CURRENT_API_SCOPES])))
      systemErrorExit(12, MESSAGE_API_ACCESS_CONFIG)
    else:
      systemErrorExit(19, MESSAGE_SERVICE_NOT_APPLICABLE.format(GM_Globals[GM_CURRENT_API_USER]))
  systemErrorExit(18, u'Authentication Token Error - {0}'.format(e))

def getSvcAcctCredentials(scopes, act_as):
  try:
    if not GM_Globals[GM_OAUTH2SERVICE_JSON_DATA]:
      json_string = readFile(GC_Values[GC_OAUTH2SERVICE_JSON], continueOnError=True, displayError=True)
      if not json_string:
        printLine(MESSAGE_INSTRUCTIONS_OAUTH2SERVICE_JSON)
        systemErrorExit(6, None)
      GM_Globals[GM_OAUTH2SERVICE_JSON_DATA] = json.loads(json_string)
    credentials = oauth2client.service_account.ServiceAccountCredentials.from_json_keyfile_dict(GM_Globals[GM_OAUTH2SERVICE_JSON_DATA], scopes)
    credentials = credentials.create_delegated(act_as)
    credentials.user_agent = GAM_INFO
    serialization_data = credentials.serialization_data
    GM_Globals[GM_OAUTH2SERVICE_ACCOUNT_CLIENT_ID] = serialization_data[u'client_id']
    return credentials
  except (ValueError, KeyError):
    printLine(MESSAGE_INSTRUCTIONS_OAUTH2SERVICE_JSON)
    invalidJSONExit(GC_Values[GC_OAUTH2SERVICE_JSON])

def getOauth2TxtStorageCredentials():
  storage = oauth2client.file.Storage(GC_Values[GC_OAUTH2_TXT])
  try:
    return (storage, storage.get())
  except (KeyError, ValueError):
    return (storage, None)

def getGDataOAuthToken(gdataObject):
  storage, credentials = getOauth2TxtStorageCredentials()
  if not credentials or credentials.invalid:
    doOAuthRequest()
    credentials = storage.get()
  try:
    if credentials.access_token_expired:
      credentials.refresh(httplib2.Http(disable_ssl_certificate_validation=GC_Values[GC_NO_VERIFY_SSL]))
  except oauth2client.client.AccessTokenRefreshError as e:
    return handleOAuthTokenError(e, False)
  gdataObject.additional_headers[u'Authorization'] = u'Bearer {0}'.format(credentials.access_token)
  if not GC_Values[GC_DOMAIN]:
    GC_Values[GC_DOMAIN] = credentials.id_token.get(u'hd', u'UNKNOWN').lower()
  if not GC_Values[GC_CUSTOMER_ID]:
    GC_Values[GC_CUSTOMER_ID] = MY_CUSTOMER
  gdataObject.domain = GC_Values[GC_DOMAIN]
  return True

def checkGDataError(e, service):
  # First check for errors that need special handling
  if e[0].get(u'reason', u'') in [u'Token invalid - Invalid token: Stateless token expired', u'Token invalid - Invalid token: Token not found']:
    keep_domain = service.domain
    getGDataOAuthToken(service)
    service.domain = keep_domain
    return (GDATA_TOKEN_EXPIRED, e[0][u'reason'])
  if e.error_code == 600:
    if e[0][u'body'].startswith(u'Quota exceeded for the current request'):
      return (GDATA_QUOTA_EXCEEDED, e[0][u'body'])
    if e[0][u'body'].startswith(u'Request rate higher than configured'):
      return (GDATA_QUOTA_EXCEEDED, e[0][u'body'])
    if e[0][u'reason'] == u'Bad Gateway':
      return (GDATA_BAD_GATEWAY, e[0][u'reason'])
    if e[0][u'reason'] == u'Service Unavailable':
      return (GDATA_SERVICE_UNAVAILABLE, e[0][u'reason'])
    if e[0][u'reason'] == u'Internal Server Error':
      return (GDATA_INTERNAL_SERVER_ERROR, e[0][u'reason'])
    if e[0][u'reason'] == u'Token invalid - Invalid token: Token disabled, revoked, or expired.':
      return (GDATA_TOKEN_INVALID, u'Token disabled, revoked, or expired. Please delete and re-create oauth.txt')
    if e[0][u'reason'] == u'Token invalid - AuthSub token has wrong scope':
      return (GDATA_INSUFFICIENT_PERMISSIONS, e[0][u'reason'])
    if e[0][u'reason'].startswith(u'Only administrators can request entries belonging to'):
      return (GDATA_INSUFFICIENT_PERMISSIONS, e[0][u'reason'])
    if e[0][u'reason'] == u'You are not authorized to access this API':
      return (GDATA_INSUFFICIENT_PERMISSIONS, e[0][u'reason'])
    if e[0][u'reason'] == u'Invalid domain.':
      return (GDATA_INVALID_DOMAIN, e[0][u'reason'])
    if e[0][u'reason'].startswith(u'You are not authorized to perform operations on the domain'):
      return (GDATA_INVALID_DOMAIN, e[0][u'reason'])
    if e[0][u'reason'] == u'Bad Request':
      if u'already exists' in e[0][u'body']:
        return (GDATA_ENTITY_EXISTS, e[0][u'body'])
      return (GDATA_BAD_REQUEST, e[0][u'body'])
    if e[0][u'reason'] == u'Forbidden':
      return (GDATA_FORBIDDEN, e[0][u'body'])
    if e[0][u'reason'] == u'Not Found':
      return (GDATA_NOT_FOUND, e[0][u'body'])
    if e[0][u'reason'] == u'Precondition Failed':
      return (GDATA_PRECONDITION_FAILED, e[0][u'reason'])
  elif e.error_code == 602:
    if e[0][u'reason'] == u'Bad Request':
      return (GDATA_BAD_REQUEST, e[0][u'body'])

  # We got a "normal" error, define the mapping below
  error_code_map = {
    1000: e[0][u'reason'],
    1001: e[0][u'reason'],
    1002: u'Unauthorized and forbidden',
    1100: u'User deleted recently',
    1200: u'Domain user limit exceeded',
    1201: u'Domain alias limit exceeded',
    1202: u'Domain suspended',
    1203: u'Domain feature unavailable',
    1300: u'Entity %s exists' % getattr(e, u'invalidInput', u'<unknown>'),
    1301: u'Entity %s Does Not Exist' % getattr(e, u'invalidInput', u'<unknown>'),
    1302: u'Entity Name Is Reserved',
    1303: u'Entity %s name not valid' % getattr(e, u'invalidInput', u'<unknown>'),
    1306: u'%s has members. Cannot delete.' % getattr(e, u'invalidInput', u'<unknown>'),
    1400: u'Invalid Given Name',
    1401: u'Invalid Family Name',
    1402: u'Invalid Password',
    1403: u'Invalid Username',
    1404: u'Invalid Hash Function Name',
    1405: u'Invalid Hash Digest Length',
    1406: u'Invalid Email Address',
    1407: u'Invalid Query Parameter Value',
    1408: u'Invalid SSO Signing Key',
    1409: u'Invalid Encryption Public Key',
    1410: u'Feature Unavailable For User',
    1500: u'Too Many Recipients On Email List',
    1501: u'Too Many Aliases For User',
    1502: u'Too Many Delegates For User',
    1601: u'Duplicate Destinations',
    1602: u'Too Many Destinations',
    1603: u'Invalid Route Address',
    1700: u'Group Cannot Contain Cycle',
    1800: u'Group Cannot Contain Cycle',
    1801: u'Invalid value %s' % getattr(e, u'invalidInput', u'<unknown>'),
  }
  return (e.error_code, error_code_map.get(e.error_code, u'Unknown Error: {0}'.format(str(e))))

def waitOnFailure(n, retries, error_code, error_message):
  wait_on_fail = min(2 ** n, 60) + float(random.randint(1, 1000)) / 1000
  if n > 3:
    sys.stderr.write(u'Temporary error: {0} - {1}. Backing off {2} seconds...'.format(error_code, error_message, int(wait_on_fail)))
  time.sleep(wait_on_fail)
  if n > 3:
    sys.stderr.write(u'attempt {0}/{1}\n'.format(n+1, retries))

class GData_badRequest(Exception):
  pass
class GData_doesNotExist(Exception):
  pass
class GData_entityExists(Exception):
  pass
class GData_forbidden(Exception):
  pass
class GData_insufficientPermissions(Exception):
  pass
class GData_internalServerError(Exception):
  pass
class GData_invalidDomain(Exception):
  pass
class GData_invalidValue(Exception):
  pass
class GData_nameNotValid(Exception):
  pass
class GData_notFound(Exception):
  pass
class GData_preconditionFailed(Exception):
  pass
class GData_serviceNotApplicable(Exception):
  pass

GDATA_ERROR_CODE_EXCEPTION_MAP = {
  GDATA_BAD_REQUEST: GData_badRequest,
  GDATA_DOES_NOT_EXIST: GData_doesNotExist,
  GDATA_ENTITY_EXISTS: GData_entityExists,
  GDATA_FORBIDDEN: GData_forbidden,
  GDATA_INSUFFICIENT_PERMISSIONS: GData_insufficientPermissions,
  GDATA_INTERNAL_SERVER_ERROR: GData_internalServerError,
  GDATA_INVALID_DOMAIN: GData_invalidDomain,
  GDATA_INVALID_VALUE: GData_invalidValue,
  GDATA_NAME_NOT_VALID: GData_nameNotValid,
  GDATA_NOT_FOUND: GData_notFound,
  GDATA_PRECONDITION_FAILED: GData_preconditionFailed,
  GDATA_SERVICE_NOT_APPLICABLE: GData_serviceNotApplicable,
  }

def callGData(service, function,
              soft_errors=False, throw_errors=None, retry_errors=None,
              **kwargs):
  import gdata.apps.service
  if throw_errors is None:
    throw_errors = []
  if retry_errors is None:
    retry_errors = []
  method = getattr(service, function)
  retries = 10
  for n in range(1, retries+1):
    try:
      return method(**kwargs)
    except gdata.apps.service.AppsForYourDomainException as e:
      error_code, error_message = checkGDataError(e, service)
      if error_code in throw_errors:
        if error_code in GDATA_ERROR_CODE_EXCEPTION_MAP:
          raise GDATA_ERROR_CODE_EXCEPTION_MAP[error_code](error_message)
        raise
      if (n != retries) and (error_code in GDATA_NON_TERMINATING_ERRORS+retry_errors):
        waitOnFailure(n, retries, error_code, error_message)
        continue
      if soft_errors:
        stderrErrorMsg(u'{0} - {1}{2}'.format(error_code, error_message, [u'', u': Giving up.\n'][n > 1]))
        return None
      systemErrorExit(GOOGLE_API_ERROR_RC, u'{0} - {1}'.format(error_code, error_message))
    except oauth2client.client.AccessTokenRefreshError as e:
      handleOAuthTokenError(e, soft_errors or GDATA_SERVICE_NOT_APPLICABLE in throw_errors)
      if GDATA_SERVICE_NOT_APPLICABLE in throw_errors:
        raise GData_serviceNotApplicable(e.message)
      entityUnknownWarning(u'User', GM_Globals[GM_CURRENT_API_USER], 0, 0)
      return None
    except socket.error as e:
      if n != retries:
        waitOnFailure(n, retries, e.errno, e.strerror)
        continue
      if soft_errors:
        stderrErrorMsg(u'{0} - {1}{2}'.format(e.errno, e.strerror, [u'', u': Giving up.\n'][n > 1]))
        return None
      systemErrorExit(SOCKET_ERROR_RC, e.strerror)

def checkGAPIError(e, soft_errors=False, silent_errors=False, retryOnHttpError=False, service=None):
  try:
    error = json.loads(e.content)
  except ValueError:
    if (e.resp[u'status'] == u'503') and (e.content.startswith(u'Quota exceeded for the current request')):
      return (e.resp[u'status'], GAPI_QUOTA_EXCEEDED, e.content)
    if (e.resp[u'status'] == u'403') and (e.content.startswith(u'Request rate higher than configured')):
      return (e.resp[u'status'], GAPI_QUOTA_EXCEEDED, e.content)
    if (e.resp[u'status'] == u'403') and (u'Invalid domain.' in e.content):
      error = {u'error': {u'code': 403, u'errors': [{u'reason': GAPI_NOT_FOUND, u'message': u'Domain not found'}]}}
    elif (e.resp[u'status'] == u'400') and (u'InvalidSsoSigningKey' in e.content):
      error = {u'error': {u'code': 400, u'errors': [{u'reason': GAPI_INVALID, u'message': u'InvalidSsoSigningKey'}]}}
    elif (e.resp[u'status'] == u'400') and (u'UnknownError' in e.content):
      error = {u'error': {u'code': 400, u'errors': [{u'reason': GAPI_INVALID, u'message': u'UnknownError'}]}}
    elif retryOnHttpError:
      service._http.request.credentials.refresh(httplib2.Http(disable_ssl_certificate_validation=GC_Values[GC_NO_VERIFY_SSL]))
      return (-1, None, None)
    elif soft_errors:
      if not silent_errors:
        stderrErrorMsg(e.content)
      return (0, None, None)
    else:
      systemErrorExit(HTTP_ERROR_RC, e.content)
  if u'error' in error:
    http_status = error[u'error'][u'code']
    try:
      message = error[u'error'][u'errors'][0][u'message']
    except KeyError:
      message = error[u'error'][u'message']
    if http_status == 500:
      if not message:
        message = PHRASE_UNKNOWN
        error = {u'error': {u'errors': [{u'reason': GAPI_UNKNOWN_ERROR, u'message': message}]}}
      elif u'Backend Error' in message:
        error = {u'error': {u'errors': [{u'reason': GAPI_BACKEND_ERROR, u'message': message}]}}
  else:
    if u'error_description' in error:
      if error[u'error_description'] == u'Invalid Value':
        message = error[u'error_description']
        http_status = 400
        error = {u'error': {u'errors': [{u'reason': GAPI_INVALID, u'message': message}]}}
      else:
        systemErrorExit(GOOGLE_API_ERROR_RC, str(error))
    else:
      systemErrorExit(GOOGLE_API_ERROR_RC, str(error))
  try:
    reason = error[u'error'][u'errors'][0][u'reason']
    if reason == GAPI_NOT_FOUND:
      if u'userKey' in message:
        reason = GAPI_USER_NOT_FOUND
      elif u'groupKey' in message:
        reason = GAPI_GROUP_NOT_FOUND
      elif u'memberKey' in message:
        reason = GAPI_MEMBER_NOT_FOUND
      elif u'Org unit not found' in message:
        reason = GAPI_ORGUNIT_NOT_FOUND
      elif u'File not found' in message:
        reason = GAPI_FILE_NOT_FOUND
      elif u'Permission not found' in message:
        reason = GAPI_PERMISSION_NOT_FOUND
      elif u'resource_id' in message:
        reason = GAPI_RESOURCE_ID_NOT_FOUND
      elif u'resourceId' in message:
        reason = GAPI_RESOURCE_ID_NOT_FOUND
      elif (u'Domain not found' in message) or (u'domain' in message):
        reason = GAPI_DOMAIN_NOT_FOUND
      elif u'Domain alias does not exist' in message:
        reason = GAPI_DOMAIN_ALIAS_NOT_FOUND
      elif u'photo' in message:
        reason = GAPI_PHOTO_NOT_FOUND
      elif u'Resource Not Found' in message:
        reason = GAPI_RESOURCE_NOT_FOUND
      elif u'Customer doesn\'t exist' in message:
        reason = GAPI_CUSTOMER_NOT_FOUND
    elif reason == GAPI_RESOURCE_NOT_FOUND:
      if u'resourceId' in message:
        reason = GAPI_RESOURCE_ID_NOT_FOUND
    elif reason == GAPI_INVALID:
      if u'userId' in message:
        reason = GAPI_USER_NOT_FOUND
      elif u'memberKey' in message:
        reason = GAPI_INVALID_MEMBER
      elif u'Invalid Ou Id' in message:
        reason = GAPI_INVALID_ORGUNIT
      elif u'Invalid Input: INVALID_OU_ID' in message:
        reason = GAPI_INVALID_ORGUNIT
      elif u'Invalid Parent Orgunit Id' in message:
        reason = GAPI_INVALID_PARENT_ORGUNIT
      elif u'Invalid scope value' in message:
        reason = GAPI_INVALID_SCOPE_VALUE
      elif u'A system error has occurred' in message:
        reason = GAPI_SYSTEM_ERROR
      elif u'Invalid Input: custom_schema' in message:
        reason = GAPI_INVALID_SCHEMA_VALUE
      elif u'New domain name is not a verified secondary domain' in message:
        reason = GAPI_DOMAIN_NOT_VERIFIED_SECONDARY
      elif u'Invalid query' in message:
        reason = GAPI_INVALID_QUERY
      elif u'Invalid Customer Id' in message:
        reason = GAPI_INVALID_CUSTOMER_ID
      elif u'Invalid Input: resource' in message:
        reason = GAPI_INVALID_RESOURCE
      elif u'Invalid Input:' in message:
        reason = GAPI_INVALID_INPUT
    elif reason == GAPI_REQUIRED:
      if u'memberKey' in message:
        reason = GAPI_MEMBER_NOT_FOUND
      elif u'Login Required' in message:
        reason = GAPI_LOGIN_REQUIRED
    elif reason == GAPI_CONDITION_NOT_MET:
      if u'undelete' in message:
        reason = GAPI_DELETED_USER_NOT_FOUND
      elif u'Cyclic memberships not allowed' in message:
        reason = GAPI_CYCLIC_MEMBERSHIPS_NOT_ALLOWED
    elif reason == GAPI_INVALID_SHARING_REQUEST:
      loc = message.find(u'User message: ')
      if loc != 1:
        message = message[loc+15:]
    elif reason == GAPI_ABORTED:
      if u'Label name exists or conflicts' in message:
        reason = GAPI_DUPLICATE
    elif reason == GAPI_FAILED_PRECONDITION:
      if u'Bad Request' in message:
        reason = GAPI_BAD_REQUEST
      elif u'Mail service not enabled' in message:
        reason = GAPI_SERVICE_NOT_AVAILABLE
    elif reason == GAPI_INVALID_ARGUMENT:
      if u'Cannot delete primary send-as' in message:
        reason = GAPI_CANNOT_DELETE_PRIMARY_SENDAS
  except KeyError:
    reason = u'{0}'.format(http_status)
  return (http_status, reason, message)

class GAPI_aborted(Exception):
  pass
class GAPI_alreadyExists(Exception):
  pass
class GAPI_authError(Exception):
  pass
class GAPI_backendError(Exception):
  pass
class GAPI_badRequest(Exception):
  pass
class GAPI_cannotChangeOwnAcl(Exception):
  pass
class GAPI_cannotChangeOwnerAcl(Exception):
  pass
class GAPI_cannotDeletePrimaryCalendar(Exception):
  pass
class GAPI_cannotDeletePrimarySendAs(Exception):
  pass
class GAPI_conditionNotMet(Exception):
  pass
class GAPI_customerNotFound(Exception):
  pass
class GAPI_cyclicMembershipsNotAllowed(Exception):
  pass
class GAPI_deleted(Exception):
  pass
class GAPI_deletedUserNotFound(Exception):
  pass
class GAPI_domainAliasNotFound(Exception):
  pass
class GAPI_domainNotFound(Exception):
  pass
class GAPI_domainNotVerifiedSecondary(Exception):
  pass
class GAPI_duplicate(Exception):
  pass
class GAPI_failedPrecondition(Exception):
  pass
class GAPI_fileNotFound(Exception):
  pass
class GAPI_forbidden(Exception):
  pass
class GAPI_groupNotFound(Exception):
  pass
class GAPI_insufficientPermissions(Exception):
  pass
class GAPI_internalError(Exception):
  pass
class GAPI_invalid(Exception):
  pass
class GAPI_invalidArgument(Exception):
  pass
class GAPI_invalidCustomerId(Exception):
  pass
class GAPI_invalidInput(Exception):
  pass
class GAPI_invalidMember(Exception):
  pass
class GAPI_invalidOrgunit(Exception):
  pass
class GAPI_invalidParentOrgunit(Exception):
  pass
class GAPI_invalidQuery(Exception):
  pass
class GAPI_invalidResource(Exception):
  pass
class GAPI_invalidSchemaValue(Exception):
  pass
class GAPI_invalidScopeValue(Exception):
  pass
class GAPI_invalidSharingRequest(Exception):
  pass
class GAPI_loginRequired(Exception):
  pass
class GAPI_memberNotFound(Exception):
  pass
class GAPI_notFound(Exception):
  pass
class GAPI_notImplemented(Exception):
  pass
class GAPI_orgunitNotFound(Exception):
  pass
class GAPI_permissionDenied(Exception):
  pass
class GAPI_permissionNotFound(Exception):
  pass
class GAPI_photoNotFound(Exception):
  pass
class GAPI_required(Exception):
  pass
class GAPI_resourceIdNotFound(Exception):
  pass
class GAPI_resourceNotFound(Exception):
  pass
class GAPI_serviceLimit(Exception):
  pass
class GAPI_serviceNotAvailable(Exception):
  pass
class GAPI_systemError(Exception):
  pass
class GAPI_timeRangeEmpty(Exception):
  pass
class GAPI_unknownError(Exception):
  pass
class GAPI_userNotFound(Exception):
  pass

GAPI_REASON_EXCEPTION_MAP = {
  GAPI_ABORTED: GAPI_aborted,
  GAPI_ALREADY_EXISTS: GAPI_alreadyExists,
  GAPI_AUTH_ERROR: GAPI_authError,
  GAPI_BACKEND_ERROR: GAPI_backendError,
  GAPI_BAD_REQUEST: GAPI_badRequest,
  GAPI_CANNOT_CHANGE_OWN_ACL: GAPI_cannotChangeOwnAcl,
  GAPI_CANNOT_CHANGE_OWNER_ACL: GAPI_cannotChangeOwnerAcl,
  GAPI_CANNOT_DELETE_PRIMARY_CALENDAR: GAPI_cannotDeletePrimaryCalendar,
  GAPI_CANNOT_DELETE_PRIMARY_SENDAS: GAPI_cannotDeletePrimarySendAs,
  GAPI_CONDITION_NOT_MET: GAPI_conditionNotMet,
  GAPI_CUSTOMER_NOT_FOUND: GAPI_customerNotFound,
  GAPI_CYCLIC_MEMBERSHIPS_NOT_ALLOWED: GAPI_cyclicMembershipsNotAllowed,
  GAPI_DELETED: GAPI_deleted,
  GAPI_DELETED_USER_NOT_FOUND: GAPI_deletedUserNotFound,
  GAPI_DOMAIN_ALIAS_NOT_FOUND: GAPI_domainAliasNotFound,
  GAPI_DOMAIN_NOT_FOUND: GAPI_domainNotFound,
  GAPI_DOMAIN_NOT_VERIFIED_SECONDARY: GAPI_domainNotVerifiedSecondary,
  GAPI_DUPLICATE: GAPI_duplicate,
  GAPI_FAILED_PRECONDITION: GAPI_failedPrecondition,
  GAPI_FILE_NOT_FOUND: GAPI_fileNotFound,
  GAPI_FORBIDDEN: GAPI_forbidden,
  GAPI_GROUP_NOT_FOUND: GAPI_groupNotFound,
  GAPI_INSUFFICIENT_PERMISSIONS: GAPI_insufficientPermissions,
  GAPI_INTERNAL_ERROR: GAPI_internalError,
  GAPI_INVALID: GAPI_invalid,
  GAPI_INVALID_ARGUMENT: GAPI_invalidArgument,
  GAPI_INVALID_CUSTOMER_ID: GAPI_invalidCustomerId,
  GAPI_INVALID_INPUT: GAPI_invalidInput,
  GAPI_INVALID_MEMBER: GAPI_invalidMember,
  GAPI_INVALID_ORGUNIT: GAPI_invalidOrgunit,
  GAPI_INVALID_PARENT_ORGUNIT: GAPI_invalidParentOrgunit,
  GAPI_INVALID_QUERY: GAPI_invalidQuery,
  GAPI_INVALID_RESOURCE: GAPI_invalidResource,
  GAPI_INVALID_SCHEMA_VALUE: GAPI_invalidSchemaValue,
  GAPI_INVALID_SCOPE_VALUE: GAPI_invalidScopeValue,
  GAPI_INVALID_SHARING_REQUEST: GAPI_invalidSharingRequest,
  GAPI_LOGIN_REQUIRED: GAPI_loginRequired,
  GAPI_MEMBER_NOT_FOUND: GAPI_memberNotFound,
  GAPI_NOT_FOUND: GAPI_notFound,
  GAPI_NOT_IMPLEMENTED: GAPI_notImplemented,
  GAPI_ORGUNIT_NOT_FOUND: GAPI_orgunitNotFound,
  GAPI_PERMISSION_DENIED: GAPI_permissionDenied,
  GAPI_PERMISSION_NOT_FOUND: GAPI_permissionNotFound,
  GAPI_PHOTO_NOT_FOUND: GAPI_photoNotFound,
  GAPI_REQUIRED: GAPI_required,
  GAPI_RESOURCE_ID_NOT_FOUND: GAPI_resourceIdNotFound,
  GAPI_RESOURCE_NOT_FOUND: GAPI_resourceNotFound,
  GAPI_SERVICE_LIMIT: GAPI_serviceLimit,
  GAPI_SERVICE_NOT_AVAILABLE: GAPI_serviceNotAvailable,
  GAPI_SYSTEM_ERROR: GAPI_systemError,
  GAPI_TIME_RANGE_EMPTY: GAPI_timeRangeEmpty,
  GAPI_UNKNOWN_ERROR: GAPI_unknownError,
  GAPI_USER_NOT_FOUND: GAPI_userNotFound,
  }

def callGAPI(service, function,
             silent_errors=False, soft_errors=False, throw_reasons=None, retry_reasons=None,
             **kwargs):
  if throw_reasons is None:
    throw_reasons = []
  if retry_reasons is None:
    retry_reasons = []
  method = getattr(service, function)
  retries = 10
  parameters = dict(kwargs.items()+GM_Globals[GM_EXTRA_ARGS_LIST])
  for n in range(1, retries+1):
    try:
      return method(**parameters).execute()
    except googleapiclient.errors.HttpError as e:
      http_status, reason, message = checkGAPIError(e, soft_errors=soft_errors, silent_errors=silent_errors, retryOnHttpError=n < 3, service=service)
      if http_status == -1:
        continue
      if http_status == 0:
        return None
      if reason in throw_reasons:
        if reason in GAPI_REASON_EXCEPTION_MAP:
          raise GAPI_REASON_EXCEPTION_MAP[reason](message)
        raise e
      if (n != retries) and (reason in GAPI_DEFAULT_RETRY_REASONS+retry_reasons):
        waitOnFailure(n, retries, reason, message)
        continue
      if soft_errors:
        stderrErrorMsg(u'{0}: {1} - {2}{3}'.format(http_status, reason, message, [u'', u': Giving up.\n'][n > 1]))
        return None
      systemErrorExit(HTTP_ERROR_RC, formatHTTPError(http_status, reason, message))
    except oauth2client.client.AccessTokenRefreshError as e:
      handleOAuthTokenError(e, soft_errors or GAPI_SERVICE_NOT_AVAILABLE in throw_reasons)
      if GAPI_SERVICE_NOT_AVAILABLE in throw_reasons:
        raise GAPI_serviceNotAvailable(e.message)
      entityUnknownWarning(u'User', GM_Globals[GM_CURRENT_API_USER], 0, 0)
      return None
    except httplib2.CertificateValidationUnsupported:
      noPythonSSLExit()
    except socket.error as e:
      if n != retries:
        waitOnFailure(n, retries, e.errno, e.strerror)
        continue
      if soft_errors:
        stderrErrorMsg(u'{0} - {1}{2}'.format(e.errno, e.strerror, [u'', u': Giving up.\n'][n > 1]))
        return None
      systemErrorExit(SOCKET_ERROR_RC, e.strerror)
    except TypeError as e:
      systemErrorExit(GOOGLE_API_ERROR_RC, e)

def callGAPIpages(service, function, items,
                  page_message=None, message_attribute=None,
                  throw_reasons=None, retry_reasons=None,
                  **kwargs):
  if throw_reasons is None:
    throw_reasons = []
  if retry_reasons is None:
    retry_reasons = []
  pageToken = None
  allResults = collections.deque()
  totalItems = 0
  while True:
    results = callGAPI(service, function, throw_reasons=throw_reasons, retry_reasons=retry_reasons, pageToken=pageToken, **kwargs)
    if results:
      pageToken = results.get(u'nextPageToken')
      if items in results:
        pageItems = len(results[items])
        totalItems += pageItems
        allResults.extend(results[items])
      else:
        results = {items: []}
        pageItems = 0
    else:
      pageToken = None
      results = {items: []}
      pageItems = 0
    if page_message:
      show_message = page_message.replace(u'%%num_items%%', str(pageItems))
      show_message = show_message.replace(u'%%total_items%%', str(totalItems))
      if message_attribute:
        try:
          show_message = show_message.replace(u'%%first_item%%', str(results[items][0][message_attribute]))
          show_message = show_message.replace(u'%%last_item%%', str(results[items][-1][message_attribute]))
        except (IndexError, KeyError):
          show_message = show_message.replace(u'%%first_item%%', u'')
          show_message = show_message.replace(u'%%last_item%%', u'')
      sys.stderr.write(u'\r')
      sys.stderr.flush()
      sys.stderr.write(show_message)
    if not pageToken:
      if page_message and (page_message[-1] != u'\n'):
        sys.stderr.write(u'\r\n')
        sys.stderr.flush()
      return allResults

def callGAPIitems(service, function, items,
                  throw_reasons=None, retry_reasons=None,
                  **kwargs):
  if throw_reasons is None:
    throw_reasons = []
  if retry_reasons is None:
    retry_reasons = []
  results = callGAPI(service, function,
                     throw_reasons=throw_reasons, retry_reasons=retry_reasons,
                     **kwargs)
  if results:
    return results.get(items, [])
  return []

GCP_MESSAGE_EXCEPTION_MAP = {
  }

def checkCloudPrintResult(result, throw_messages=None):
  if throw_messages is None:
    throw_messages = []
  if isinstance(result, str):
    try:
      result = json.loads(result)
    except ValueError:
      systemErrorExit(JSON_LOADS_ERROR_RC, result)
  if not result[u'success']:
    message = result[u'message']
    if message in throw_messages:
      if message in GCP_MESSAGE_EXCEPTION_MAP:
        raise GCP_MESSAGE_EXCEPTION_MAP[message](message)
    systemErrorExit(AC_FAILED_RC, u'{0}: {1}'.format(result[u'errorCode'], result[u'message']))
  return result

def callGCP(service, function,
            throw_messages=None,
            **kwargs):
  result = callGAPI(service, function,
                    **kwargs)
  return checkCloudPrintResult(result, throw_messages=throw_messages)

API_VER_MAPPING = {
  GAPI_ADMIN_SETTINGS_API: u'v2',
  GAPI_APPSACTIVITY_API: u'v1',
  GAPI_CALENDAR_API: u'v3',
  GAPI_CLASSROOM_API: u'v1',
  GAPI_CLOUDPRINT_API: u'v2',
  GAPI_DATATRANSFER_API: u'datatransfer_v1',
  GAPI_DIRECTORY_API: u'directory_v1',
  GAPI_DRIVE_API: u'v2',
  GDATA_EMAIL_AUDIT_API: u'v1',
  GAPI_EMAIL_SETTINGS_API: u'v2',
  GAPI_GMAIL_API: u'v1',
  GAPI_GPLUS_API: u'v1',
  GAPI_GROUPSSETTINGS_API: u'v1',
  GAPI_LICENSING_API: u'v1',
  GAPI_OAUTH2_API: u'v2',
  GAPI_REPORTS_API: u'reports_v1',
  GAPI_SITEVERIFICATION_API: u'v1',
  }

def getAPIVersion(api):
  version = API_VER_MAPPING.get(api, u'v1')
  if api in [GAPI_DIRECTORY_API, GAPI_REPORTS_API, GAPI_DATATRANSFER_API]:
    api = u'admin'
  return (api, version, u'{0}-{1}'.format(api, version))

def readDiscoveryFile(api_version):
  disc_filename = u'%s.json' % (api_version)
  disc_file = os.path.join(GM_Globals[GM_GAM_PATH], disc_filename)
  if hasattr(sys, u'_MEIPASS'):
    pyinstaller_disc_file = os.path.join(sys._MEIPASS, disc_filename)
  else:
    pyinstaller_disc_file = None
  if os.path.isfile(disc_file):
    json_string = readFile(disc_file)
  elif pyinstaller_disc_file:
    json_string = readFile(pyinstaller_disc_file)
  else:
    systemErrorExit(11, MESSAGE_NO_DISCOVERY_INFORMATION.format(disc_file))
  try:
    discovery = json.loads(json_string)
    return (disc_file, discovery)
  except ValueError:
    invalidJSONExit(disc_file)

def getClientAPIversionHttpService(api):
  storage, credentials = getOauth2TxtStorageCredentials()
  if not credentials or credentials.invalid:
    doOAuthRequest()
    credentials = storage.get()
  credentials.user_agent = GAM_INFO
  api, version, api_version = getAPIVersion(api)
  http = credentials.authorize(httplib2.Http(disable_ssl_certificate_validation=GC_Values[GC_NO_VERIFY_SSL],
                                             cache=GM_Globals[GM_CACHE_DIR]))
  try:
    service = googleapiclient.discovery.build(api, version, http=http, cache_discovery=False)
    if GM_Globals[GM_CACHE_DISCOVERY_ONLY]:
      http.cache = None
    return (credentials, service)
  except httplib2.ServerNotFoundError as e:
    systemErrorExit(4, e)
  except httplib2.CertificateValidationUnsupported:
    noPythonSSLExit()
  except googleapiclient.errors.UnknownApiNameOrVersion:
    pass
  disc_file, discovery = readDiscoveryFile(api_version)
  try:
    service = googleapiclient.discovery.build_from_document(discovery, http=http)
    if GM_Globals[GM_CACHE_DISCOVERY_ONLY]:
      http.cache = None
    return (credentials, service)
  except (ValueError, KeyError):
    invalidJSONExit(disc_file)

def buildGAPIObject(api):
  GM_Globals[GM_CURRENT_API_USER] = None
  credentials, service = getClientAPIversionHttpService(api)
  if GC_Values[GC_DOMAIN]:
    if not GC_Values[GC_CUSTOMER_ID]:
      resp, result = service._http.request(u'https://www.googleapis.com/admin/directory/v1/users?domain={0}&maxResults=1&fields=users(customerId)'.format(GC_Values[GC_DOMAIN]))
      try:
        resultObj = json.loads(result)
      except ValueError:
        systemErrorExit(8, u'Unexpected response: {0}'.format(result))
      if resp[u'status'] in [u'403', u'404']:
        try:
          message = resultObj[u'error'][u'errors'][0][u'message']
        except KeyError:
          message = resultObj[u'error'][u'message']
        systemErrorExit(8, u'{0} - {1}'.format(message, GC_Values[GC_DOMAIN]))
      try:
        GC_Values[GC_CUSTOMER_ID] = resultObj[u'users'][0][u'customerId']
      except KeyError:
        GC_Values[GC_CUSTOMER_ID] = MY_CUSTOMER
  else:
    GC_Values[GC_DOMAIN] = credentials.id_token.get(u'hd', u'UNKNOWN').lower()
    if not GC_Values[GC_CUSTOMER_ID]:
      GC_Values[GC_CUSTOMER_ID] = MY_CUSTOMER
  return service

# Convert User UID to email address
def convertUserUIDtoEmailAddress(emailAddressOrUID):
  normalizedEmailAddressOrUID = normalizeEmailAddressOrUID(emailAddressOrUID)
  if normalizedEmailAddressOrUID.find(u'@') > 0:
    return normalizedEmailAddressOrUID
  try:
    cd = buildGAPIObject(GAPI_DIRECTORY_API)
    result = callGAPI(cd.users(), u'get',
                      throw_reasons=[GAPI_USER_NOT_FOUND],
                      userKey=normalizedEmailAddressOrUID, fields=u'primaryEmail')
    if u'primaryEmail' in result:
      return result[u'primaryEmail'].lower()
  except GAPI_userNotFound:
    pass
  return normalizedEmailAddressOrUID

API_SCOPE_MAPPING = {
  GAPI_APPSACTIVITY_API: [u'https://www.googleapis.com/auth/activity',
                          u'https://www.googleapis.com/auth/drive'],
  GAPI_CALENDAR_API: [u'https://www.googleapis.com/auth/calendar',],
  GAPI_DRIVE_API: [u'https://www.googleapis.com/auth/drive',],
  GAPI_GMAIL_API: [u'https://mail.google.com/',
                   u'https://www.googleapis.com/auth/gmail.settings.basic',
                   u'https://www.googleapis.com/auth/gmail.settings.sharing',],
  GAPI_GPLUS_API: [u'https://www.googleapis.com/auth/plus.me',
                   u'https://www.googleapis.com/auth/plus.login',
                   u'https://www.googleapis.com/auth/userinfo.email',
                   u'https://www.googleapis.com/auth/userinfo.profile'],
  }

def getSvcAcctAPIversionHttpService(api):
  api, version, api_version = getAPIVersion(api)
  http = httplib2.Http(disable_ssl_certificate_validation=GC_Values[GC_NO_VERIFY_SSL],
                       cache=GM_Globals[GM_CACHE_DIR])
  try:
    service = googleapiclient.discovery.build(api, version, http=http, cache_discovery=False)
    if GM_Globals[GM_CACHE_DISCOVERY_ONLY]:
      http.cache = None
    return (api_version, http, service)
  except httplib2.ServerNotFoundError as e:
    systemErrorExit(4, e)
  except googleapiclient.errors.UnknownApiNameOrVersion:
    pass
  disc_file, discovery = readDiscoveryFile(api_version)
  try:
    service = googleapiclient.discovery.build_from_document(discovery, http=http)
    if GM_Globals[GM_CACHE_DISCOVERY_ONLY]:
      http.cache = None
    return (api_version, http, service)
  except (ValueError, KeyError):
    invalidJSONExit(disc_file)

def buildGAPIServiceObject(api, act_as, use_scopes=None):
  _, http, service = getSvcAcctAPIversionHttpService(api)
  GM_Globals[GM_CURRENT_API_USER] = act_as
  GM_Globals[GM_CURRENT_API_SCOPES] = use_scopes or API_SCOPE_MAPPING[api]
  credentials = getSvcAcctCredentials(GM_Globals[GM_CURRENT_API_SCOPES], act_as)
  try:
    service._http = credentials.authorize(http)
  except httplib2.ServerNotFoundError as e:
    systemErrorExit(4, e)
  except oauth2client.client.AccessTokenRefreshError as e:
    entityServiceNotApplicableWarning([u'Calendar', u'User'][api != GAPI_CALENDAR_API], act_as, 0, 0)
    return handleOAuthTokenError(e, True)
  return service

def buildActivityGAPIObject(user):
  userEmail = convertUserUIDtoEmailAddress(user)
  return (userEmail, buildGAPIServiceObject(GAPI_APPSACTIVITY_API, userEmail))

def buildCalendarGAPIObject(calname):
  calendarId = convertUserUIDtoEmailAddress(calname)
  return (calendarId, buildGAPIServiceObject(GAPI_CALENDAR_API, calendarId))

def buildDriveGAPIObject(user):
  userEmail = convertUserUIDtoEmailAddress(user)
  return (userEmail, buildGAPIServiceObject(GAPI_DRIVE_API, userEmail))

def buildGmailGAPIObject(user):
  userEmail = convertUserUIDtoEmailAddress(user)
  return (userEmail, buildGAPIServiceObject(GAPI_GMAIL_API, userEmail))

def buildGplusGAPIObject(user):
  userEmail = convertUserUIDtoEmailAddress(user)
  return (userEmail, buildGAPIServiceObject(GAPI_GPLUS_API, userEmail))

def initGDataObject(gdataObj, api):
  _, _, api_version = getAPIVersion(api)
  disc_file, discovery = readDiscoveryFile(api_version)
  GM_Globals[GM_CURRENT_API_USER] = None
  try:
    GM_Globals[GM_CURRENT_API_SCOPES] = discovery[u'auth'][u'oauth2'][u'scopes'].keys()
  except KeyError:
    invalidJSONExit(disc_file)
  if not getGDataOAuthToken(gdataObj):
    doOAuthRequest()
    getGDataOAuthToken(gdataObj)
  gdataObj.source = GAM_INFO
  if GC_Values[GC_DEBUG_LEVEL] > 0:
    gdataObj.debug = True
  return gdataObj

def getAdminSettingsObject():
  import gdata.apps.adminsettings.service
  return initGDataObject(gdata.apps.adminsettings.service.AdminSettingsService(), GAPI_ADMIN_SETTINGS_API)

def getAuditObject():
  import gdata.apps.audit.service
  return initGDataObject(gdata.apps.audit.service.AuditService(), GDATA_EMAIL_AUDIT_API)

def getEmailSettingsObject():
  import gdata.apps.emailsettings.service
  return initGDataObject(gdata.apps.emailsettings.service.EmailSettingsService(), GDATA_EMAIL_SETTINGS_API)

def geturl(url, dst):
  import urllib2
  u = urllib2.urlopen(url)
  f = openFile(dst, u'wb')
  meta = u.info()
  try:
    file_size = int(meta.getheaders(u'Content-Length')[0])
  except IndexError:
    file_size = -1
  file_size_dl = 0
  block_sz = 8192
  while True:
    filebuff = u.read(block_sz)
    if not filebuff:
      break
    file_size_dl += len(filebuff)
    f.write(filebuff)
    if file_size != -1:
      status = r"%10d  [%3.2f%%]" % (file_size_dl, file_size_dl * 100. / file_size)
    else:
      status = r"%10d [unknown size]" % (file_size_dl)
    status = status + chr(8)*(len(status)+1)
    print status,
  closeFile(f)

def convertEmailToUserID(user):
  if user.find(u'@') == -1:
    return user
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  try:
    return callGAPI(cd.users(), u'get', throw_reasons=[GAPI_NOT_FOUND, GAPI_FORBIDDEN], userKey=user, fields=u'id')[u'id']
  except (GAPI_notFound, GAPI_forbidden):
    usageErrorExit(u'No such user {0}'.format(user))

def convertUserIDtoEmail(uid):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  try:
    return callGAPI(cd.users(), u'get', throw_reasons=[GAPI_NOT_FOUND], userKey=uid, fields=u'primaryEmail')[u'primaryEmail']
  except GAPI_notFound:
    return u'uid:{0}'.format(uid)
#
# Add domain to foo or convert uid:xxx to foo
# Return (foo@bar.com, foo, bar.com)
def splitEmailAddressOrUID(emailAddressOrUID):
  normalizedEmailAddressOrUID = normalizeEmailAddressOrUID(emailAddressOrUID)
  atLoc = normalizedEmailAddressOrUID.find(u'@')
  if atLoc > 0:
    return (normalizedEmailAddressOrUID, normalizedEmailAddressOrUID[:atLoc], normalizedEmailAddressOrUID[atLoc+1:])
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  try:
    result = callGAPI(cd, u'get',
                      throw_reasons=[GAPI_USER_NOT_FOUND],
                      userKey=normalizedEmailAddressOrUID, fields=u'primaryEmail')
    normalizedEmailAddressOrUID = result[u'primaryEmail'].lower()
    atLoc = normalizedEmailAddressOrUID.find(u'@')
    return (normalizedEmailAddressOrUID, normalizedEmailAddressOrUID[:atLoc], normalizedEmailAddressOrUID[atLoc+1:])
  except GAPI_userNotFound:
    return (normalizedEmailAddressOrUID, normalizedEmailAddressOrUID, GC_Values[GC_DOMAIN])
#
# Add domain to foo or convert uid:xxx to foo
# Return foo@bar.com
def addDomainToEmailAddressOrUID(emailAddressOrUID, addDomain):
  cg = UID_PATTERN.match(emailAddressOrUID)
  if cg:
    try:
      cd = buildGAPIObject(GAPI_DIRECTORY_API)
      result = callGAPI(cd.users(), u'get',
                        throw_reasons=[GAPI_USER_NOT_FOUND],
                        userKey=cg.group(1), fields=u'primaryEmail')
      if u'primaryEmail' in result:
        return result[u'primaryEmail'].lower()
    except GAPI_userNotFound:
      pass
    return cg.group(1)
  atLoc = emailAddressOrUID.find(u'@')
  if atLoc == -1:
    return u'{0}@{1}'.format(emailAddressOrUID, addDomain)
  if atLoc == len(emailAddressOrUID)-1:
    return u'{0}{1}'.format(emailAddressOrUID, addDomain)
  return emailAddressOrUID

def shlexSplitList(entity, dataDelimiter=' ,'):
  import shlex
  lexer = shlex.shlex(entity, posix=True)
  lexer.whitespace = dataDelimiter
  lexer.whitespace_split = True
  return list(lexer)

def splitEntityList(entity, dataDelimiter, shlexSplit):
  if not entity:
    return []
  if not dataDelimiter:
    return [entity,]
  if not shlexSplit:
    return entity.split(dataDelimiter)
  return shlexSplitList(entity, dataDelimiter)

def getUsersToModify(entityType, entity, silent=False, member_type=None, checkNotSuspended=False):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  if entityType == u'user':
    users = [entity,]
  elif entityType == u'users':
    users = entity.replace(u',', u' ').split()
  elif entityType == u'group':
    group = normalizeEmailAddressOrUID(entity)
    if member_type is None:
      member_type_message = u'all members'
    else:
      member_type_message = u'%ss' % member_type.lower()
    page_message = None
    if not silent:
      sys.stderr.write(u"Getting %s of %s (may take some time for large groups)...\n" % (member_type_message, group))
      page_message = u'Got %%%%total_items%%%% %s...' % member_type_message
    members = callGAPIpages(cd.members(), u'list', u'members',
                            page_message=page_message,
                            groupKey=group, roles=member_type, fields=u'nextPageToken,members(email)', maxResults=GC_Values[GC_MEMBER_MAX_RESULTS])
    users = [member[u'email'] for member in members]
  elif entityType in [u'ou', u'org']:
    ou = makeOrgUnitPathAbsolute(entity)
    users = []
    page_message = None
    if not silent:
      sys.stderr.write(u"Getting all users in the G Suite organization (may take some time on a large domain)...\n")
      page_message = u'Got %%total_items%% users...'
    members = callGAPIpages(cd.users(), u'list', u'users', page_message=page_message,
                            customer=GC_Values[GC_CUSTOMER_ID], fields=u'nextPageToken,users(primaryEmail,suspended,orgUnitPath)',
                            query=u"orgUnitPath='%s'" % ou, maxResults=GC_Values[GC_USER_MAX_RESULTS])
    for member in members:
      if ou.lower() != member[u'orgUnitPath'].lower():
        continue
      if not checkNotSuspended or not member[u'suspended']:
        users.append(member[u'primaryEmail'])
    if not silent:
      sys.stderr.write(u"%s users are directly in the OU.\n" % len(users))
  elif entityType in [u'ou_and_children', u'ou_and_child']:
    ou = makeOrgUnitPathAbsolute(entity)
    users = []
    page_message = None
    if not silent:
      sys.stderr.write(u"Getting all users in the G Suite organization (may take some time on a large domain)...\n")
      page_message = u'Got %%total_items%% users..'
    members = callGAPIpages(cd.users(), u'list', u'users', page_message=page_message,
                            customer=GC_Values[GC_CUSTOMER_ID], fields=u'nextPageToken,users(primaryEmail,suspended)',
                            query=u"orgUnitPath='%s'" % ou, maxResults=GC_Values[GC_USER_MAX_RESULTS])
    for member in members:
      if not checkNotSuspended or not member[u'suspended']:
        users.append(member[u'primaryEmail'])
    if not silent:
      sys.stderr.write(u"done.\r\n")
  elif entityType == u'query':
    users = []
    if not silent:
      sys.stderr.write(u"Getting all users that match query %s (may take some time on a large domain)...\n" % entity)
    page_message = u'Got %%total_items%% users...'
    members = callGAPIpages(cd.users(), u'list', u'users', page_message=page_message,
                            customer=GC_Values[GC_CUSTOMER_ID], fields=u'nextPageToken,users(primaryEmail,suspended)',
                            query=entity, maxResults=GC_Values[GC_USER_MAX_RESULTS])
    for member in members:
      if not checkNotSuspended or not member[u'suspended']:
        users.append(member[u'primaryEmail'])
    if not silent:
      sys.stderr.write(u"done.\r\n")
  elif entityType in [u'license', u'licenses', u'licence', u'licences']:
    users = []
    licenses = doPrintLicenses(return_list=True, skus=entity.split(u','))
    for row in licenses:
      try:
        users.append(row[u'userId'])
      except KeyError:
        pass
  elif entityType == u'file':
    users = []
    encoding = getCharSet()
    dataDelimiter = getDelimiter()
    f = openFile(entity)
    uf = UTF8Recoder(f, encoding) if encoding != u'utf-8' else f
    for row in uf:
      for user in splitEntityList(row.strip(), dataDelimiter, False):
        user = user.strip()
        if user:
          users.append(user)
    closeFile(f)
  elif entityType in [u'csv', u'csvfile']:
    try:
      fileFieldNameList = entity.split(u':')
    except ValueError:
      fileFieldNameList = []
    if len(fileFieldNameList) < 2:
      putArgumentBack()
      invalidArgumentExit(OB_FILE_NAME_FIELD_NAME)
    f, csvFile = openCSVFileReader(fileFieldNameList[0])
    for fieldName in fileFieldNameList[1:]:
      if fieldName not in csvFile.fieldnames:
        csvFieldErrorExit(fieldName, csvFile.fieldnames, backupArg=True, checkForCharset=True)
    matchFields = getMatchFields(csvFile.fieldnames)
    dataDelimiter = getDelimiter()
    users = []
    for row in csvFile:
      if not matchFields or checkMatchFields(row, matchFields):
        for fieldName in fileFieldNameList[1:]:
          for user in splitEntityList(row[fieldName].strip(), dataDelimiter, False):
            user = user.strip()
            if user:
              users.append(user)
    closeFile(f)
  elif entityType in [u'courseparticipants', u'teachers', u'students']:
    croom = buildGAPIObject(GAPI_CLASSROOM_API)
    users = []
    entity = addCourseIdScope(entity)
    if entityType in [u'courseparticipants', u'teachers']:
      page_message = u'Got %%total_items%% teachers...'
      teachers = callGAPIpages(croom.courses().teachers(), u'list', u'teachers', page_message=page_message, courseId=entity)
      for teacher in teachers:
        email = teacher[u'profile'].get(u'emailAddress', None)
        if email:
          users.append(email)
    if entityType in [u'courseparticipants', u'students']:
      page_message = u'Got %%total_items%% students...'
      students = callGAPIpages(croom.courses().students(), u'list', u'students', page_message=page_message, courseId=entity)
      for student in students:
        email = student[u'profile'].get(u'emailAddress', None)
        if email:
          users.append(email)
  elif entityType == u'all':
    users = []
    if entity.lower() == u'users':
      if not silent:
        sys.stderr.write(u"Getting all users in G Suite account (may take some time on a large account)...\n")
      page_message = u'Got %%total_items%% users...'
      all_users = callGAPIpages(cd.users(), u'list', u'users', page_message=page_message,
                                customer=GC_Values[GC_CUSTOMER_ID],
                                fields=u'nextPageToken,users(primaryEmail,suspended)', maxResults=GC_Values[GC_USER_MAX_RESULTS])
      for member in all_users:
        if not member[u'suspended']:
          users.append(member[u'primaryEmail'])
      if not silent:
        sys.stderr.write(u"done getting %s users.\r\n" % len(users))
    elif entity.lower() == u'cros':
      if not silent:
        sys.stderr.write(u"Getting all CrOS devices in G Suite account (may take some time on a large account)...\n")
      all_cros = callGAPIpages(cd.chromeosdevices(), u'list', u'chromeosdevices',
                               customerId=GC_Values[GC_CUSTOMER_ID], fields=u'nextPageToken,chromeosdevices(deviceId)',
                               maxResults=GC_Values[GC_DEVICE_MAX_RESULTS])
      for member in all_cros:
        users.append(member[u'deviceId'])
      if not silent:
        sys.stderr.write(u"done getting %s CrOS devices.\r\n" % len(users))
    else:
      putArgumentBack()
      invalidChoiceExit([u'users', u'cros'])
  elif entityType == u'cros':
    users = entity.replace(u',', u' ').split()
    entity = u'cros'
  else:
    putArgumentBack()
    unknownArgumentExit()
  return users

def getEntityToModify(crosAllowed=False, checkNotSuspended=False):
  entityTypes = usergroup_types[:]
  if not crosAllowed:
    entityTypes.remove(u'cros')
  entityType = getChoice(entityTypes, defaultChoice=u'user')
  entity = getString(OB_ENTITY)
  if (not crosAllowed) and (entityType == u'all') and (entity == u'cros'):
    putArgumentBack()
    invalidChoiceExit([u'users',])
  if (entityType == u'cros') or ((entityType == u'all') and (entity == u'cros')):
    return_type = u'cros'
  else:
    return_type = u'users'
  return (return_type, getUsersToModify(entityType, entity, checkNotSuspended=checkNotSuspended))

# Send an email
def send_email(msg_subj, msg_txt, msg_rcpt=None):
  from email.mime.text import MIMEText
  gmail = buildGAPIObject(GAPI_GMAIL_API)
  sender_email = gmail._http.request.credentials.id_token[u'email']
  if not msg_rcpt:
    msg_rcpt = sender_email
  msg = MIMEText(msg_txt)
  msg[u'Subject'] = msg_subj
  msg[u'From'] = sender_email
  msg[u'To'] = msg_rcpt
  callGAPI(gmail.users().messages(), u'send',
           userId=sender_email, body={u'raw': base64.urlsafe_b64encode(msg.as_string())})

# Write a CSV file
def addTitleToCSVfile(title, titles):
  titles.append(title)

def addTitlesToCSVfile(addTitles, titles):
  for title in addTitles:
    if title not in titles:
      addTitleToCSVfile(title, titles)

def removeTitlesFromCSVfile(removeTitles, titles):
  for title in removeTitles:
    if title in titles:
      titles.remove(title)

def addRowTitlesToCSVfile(row, csvRows, titles):
  csvRows.append(row)
  for title in row:
    if title not in titles:
      addTitleToCSVfile(title, titles)

# fieldName is command line argument
# fieldNameMap maps fieldName to API field names; CSV file header will be API field name
#ARGUMENT_TO_PROPERTY_MAP = {
#  u'admincreated': [u'adminCreated'],
#  u'aliases': [u'aliases', u'nonEditableAliases'],
#  }
# fieldsList is the list of API fields
# fieldsTitles maps the API field name to the CSV file header
def addFieldToCSVfile(fieldName, fieldNameMap, fieldsList, fieldsTitles, titles):
  for ftList in fieldNameMap[fieldName]:
    if ftList not in fieldsTitles:
      fieldsList.append(ftList)
      fieldsTitles[ftList] = ftList
      addTitlesToCSVfile([ftList], titles)

# fieldName is command line argument
# fieldNameTitleMap maps fieldName to API field name and CSV file header
#ARGUMENT_TO_PROPERTY_TITLE_MAP = {
#  u'admincreated': [u'adminCreated', u'Admin_Created'],
#  u'aliases': [u'aliases', u'Aliases', u'nonEditableAliases', u'NonEditableAliases'],
#  }
# fieldsList is the list of API fields
# fieldsTitles maps the API field name to the CSV file header
def addFieldTitleToCSVfile(fieldName, fieldNameTitleMap, fieldsList, fieldsTitles, titles):
  ftList = fieldNameTitleMap[fieldName]
  for i in range(0, len(ftList), 2):
    if ftList[i] not in fieldsTitles:
      fieldsList.append(ftList[i])
      fieldsTitles[ftList[i]] = ftList[i+1]
      addTitlesToCSVfile([ftList[i+1]], titles)

def sortCSVTitles(firstTitle, titles):
  restoreTitles = []
  for title in firstTitle:
    if title in titles:
      titles.remove(title)
      restoreTitles.append(title)
  titles.sort()
  for title in restoreTitles[::-1]:
    titles.insert(0, title)

def writeCSVfile(csvRows, titles, list_type, todrive):
  csv.register_dialect(u'nixstdout', lineterminator=u'\n')
  if todrive:
    string_file = StringIO.StringIO()
    writer = csv.DictWriter(string_file, fieldnames=titles,
                            dialect=u'nixstdout', quoting=csv.QUOTE_MINIMAL, delimiter=str(GC_Values[GC_CSV_OUTPUT_COLUMN_DELIMITER]))
  else:
    writer = csv.DictWriter(sys.stdout, fieldnames=titles,
                            dialect=u'nixstdout', quoting=csv.QUOTE_MINIMAL, delimiter=str(GC_Values[GC_CSV_OUTPUT_COLUMN_DELIMITER]))
  try:
    writer.writerow(dict((item, item) for item in writer.fieldnames))
    writer.writerows(csvRows)
  except IOError as e:
    systemErrorExit(6, e)
  if todrive:
    columns = len(csvRows[0])
    rows = len(csvRows)
    cell_count = rows * columns
    convert = True
    if cell_count > 500000 or columns > 256:
      print u'{0}{1}'.format(WARNING_PREFIX, MESSAGE_RESULTS_TOO_LARGE_FOR_GOOGLE_SPREADSHEET)
      convert = False
    drive = buildGAPIObject(GAPI_DRIVE_API)
    result = callGAPI(drive.files(), DRIVE_CREATE_FILE,
                      convert=convert, body={u'description': u' '.join(CL_argv), DRIVE_FILE_NAME: u'{0} - {1}'.format(GC_Values[GC_DOMAIN], list_type), u'mimeType': u'text/csv'},
                      media_body=googleapiclient.http.MediaInMemoryUpload(string_file.getvalue(), mimetype=u'text/csv'))
    file_url = result[DRIVE_FILE_VIEW_LINK]
    if GC_Values[GC_NO_BROWSER]:
      msg_txt = u'Drive file uploaded to:\n %s' % file_url
      msg_subj = u'%s - %s' % (GC_Values[GC_DOMAIN], list_type)
      send_email(msg_subj, msg_txt)
      print msg_txt
    else:
      import webbrowser
      webbrowser.open(file_url)

def convertCRsNLs(value):
  return value.replace(u'\r', u'\\r').replace(u'\n', u'\\n')

def flattenJSON(structure, key=u'', path=u'', flattened=None, listLimit=None):
  if flattened is None:
    flattened = {}
  if not isinstance(structure, (dict, list)):
    if isinstance(structure, (str, unicode)) and GC_Values[GC_CSV_OUTPUT_CONVERT_CR_NL]:
      flattened[((path+u'.') if path else u'')+key] = convertCRsNLs(structure)
    else:
      flattened[((path+u'.') if path else u'')+key] = structure
  elif isinstance(structure, list):
    listLen = len(structure)
    listLen = min(listLen, listLimit or listLen)
    flattened[((path+u'.') if path else u'')+key] = listLen
    for i in xrange(listLen):
      flattenJSON(structure[i], u'{0}'.format(i), u'.'.join([item for item in [path, key] if item]), flattened, listLimit)
  else:
    for new_key, value in structure.items():
      if new_key in [u'kind', u'etag']:
        continue
      if value == NEVER_TIME:
        value = u'Never'
      flattenJSON(value, new_key, u'.'.join([item for item in [path, key] if item]), flattened, listLimit)
  return flattened

def showJSON(object_name, object_value, skip_objects=None, level=0, spacing=u''):
  if skip_objects is None:
    skip_objects = []
  if object_name in [u'kind', u'etag', u'etags'] or object_name in skip_objects:
    return
  if object_name is not None:
    printJSONKey(spacing, object_name)
  if isinstance(object_value, list):
    if len(object_value) == 1 and isinstance(object_value[0], (str, unicode, int, bool)):
      if object_name is not None:
        printJSONValue(object_value[0])
      else:
        printKeyValueList(spacing, [object_value[0]])
      return
    if object_name is not None:
      printBlankLine()
      spacing += u'  '
    for sub_value in object_value:
      if isinstance(sub_value, (str, unicode, int, bool)):
        printKeyValueList(spacing, [sub_value])
      else:
        showJSON(None, sub_value, skip_objects, level=level+1, spacing=spacing)
    if object_name is not None:
      spacing = spacing[:-2]
  elif isinstance(object_value, dict):
    indentAfterFirst = unindentAfterLast = False
    if object_name is not None:
      printBlankLine()
      spacing += u'  '
    elif level > 0:
      indentAfterFirst = unindentAfterLast = True
    for sub_object in sorted(object_value):
      showJSON(sub_object, object_value[sub_object], skip_objects, level=level+1, spacing=spacing)
      if sub_object not in skip_objects:
        if indentAfterFirst:
          spacing += u'  '
          indentAfterFirst = False
    if object_name is not None or unindentAfterLast:
      spacing = spacing[:-2]
  else:
    if isinstance(object_value, (str, unicode)) and object_value.find(u'\n') >= 0:
      if GC_Values[GC_SHOW_CONVERT_CR_NL]:
        printJSONValue(convertCRsNLs(object_value))
      else:
        printBlankLine()
        spacing += u'  '
        printKeyValueList(spacing, [indentMultiLineText(object_value)])
        spacing = spacing[:-2]
    else:
      printJSONValue(object_value)

def doVersion(checkForArgs=True):
  forceCheck = simple = False
  if checkForArgs:
    while CL_argvI < CL_argvLen:
      myarg = getArgument()
      if myarg == u'check':
        forceCheck = True
      elif myarg == u'simple':
        simple = True
      else:
        unknownArgumentExit()
  if simple:
    sys.stdout.write(__version__)
    return
  import struct
  version_data = u'GAM {0} - {1}\n{2}\nPython {3}.{4}.{5} {6}-bit {7}\ngoogle-api-python-client {8}\n{9} {10}\nPath: {11}'
  print version_data.format(__version__, GAM_URL, __author__, sys.version_info[0],
                            sys.version_info[1], sys.version_info[2], struct.calcsize(u'P')*8,
                            sys.version_info[3], googleapiclient.__version__, platform.platform(),
                            platform.machine(), GM_Globals[GM_GAM_PATH])
  if forceCheck:
    doGAMCheckForUpdates(forceCheck=True)

def showUsage():
  doVersion(checkForArgs=False)
  print u'''
Usage: gam [OPTIONS]...

GAM. Retrieve or set G Suite domain,
user, group and alias settings. Exhaustive list of commands
can be found at: https://github.com/jay0lee/GAM/wiki

Examples:
gam info domain
gam create user jsmith firstname John lastname Smith password secretpass
gam update user jsmith suspended on
gam.exe update group announcements add member jsmith
...

'''

def run_batch(items):
  from multiprocessing import Pool
  num_worker_threads = min(len(items), GC_Values[GC_NUM_THREADS])
  pool = Pool(processes=num_worker_threads)
  sys.stderr.write(u'Using %s processes...\n' % num_worker_threads)
  for item in items:
    if item[0] == u'commit-batch':
      sys.stderr.write(u'commit-batch - waiting for running processes to finish before proceeding...')
      pool.close()
      pool.join()
      pool = Pool(processes=num_worker_threads)
      sys.stderr.write(u'done with commit-batch\n')
      continue
    pool.apply_async(ProcessGAMCommandNoQueue, [item])
  pool.close()
  pool.join()

def doBatch():
  import shlex
  filename = getString(OB_FILE_NAME)
  if (filename == u'-') and (GC_Values[GC_DEBUG_LEVEL] > 0):
    putArgumentBack()
    usageErrorExit(MESSAGE_BATCH_CSV_DASH_DEBUG_INCOMPATIBLE.format(u'batch'))
  encoding = getCharSet()
  checkForExtraneousArguments()
  items = []
  f = openFile(filename)
  batchFile = UTF8Recoder(f, encoding) if encoding != u'utf-8' else f
  try:
    for line in batchFile:
      argv = shlex.split(line)
      if not argv:
        continue
      cmd = argv[0].strip().lower()
      if (not cmd) or cmd.startswith(u'#') or ((len(argv) == 1) and (cmd != COMMIT_BATCH_CMD)):
        continue
      if cmd == GAM_CMD:
        items.append([arg.encode(GM_Globals[GM_SYS_ENCODING]) for arg in argv])
      elif cmd == COMMIT_BATCH_CMD:
        items.append([cmd])
      else:
        sys.stderr.write(u'Command: >>>{0}<<< {1}\n'.format(makeQuotedList([argv[0]]), makeQuotedList(argv[1:])))
        stderrErrorMsg(u'{0}: {1} <{2}>'.format(ARGUMENT_ERROR_NAMES[ARGUMENT_INVALID][1],
                                                PHRASE_EXPECTED,
                                                formatChoiceList([GAM_CMD, COMMIT_BATCH_CMD])))
  except IOError as e:
    systemErrorExit(FILE_ERROR_RC, e)
  closeFile(f)
  run_batch(items)

def runCmdForUsers(cmd, users, **kwargs):
  if (GC_Values[GC_AUTO_BATCH_MIN] < 0) and (len(users) > -GC_Values[GC_AUTO_BATCH_MIN]):
    run_batch([[u'gam', u'user', user]+CL_argv[CL_argvI-1:] for user in users])
  else:
    cmd(users, **kwargs)

# Process command line arguments, find substitutions
# An argument containing instances of ~~xxx~!~pattern~!~replacement~~ has ~~...~~ replaced by re.sub(pattern, replacement, value of field xxx from the CSV file)
# For example, ~~primaryEmail~!~^(.+)@(.+)$~!~\1 AT \2~~ would replace foo@bar.com (from the primaryEmail column) with foo AT bar.com
# An argument containing instances of ~~xxx~~ has xxx replaced by the value of field xxx from the CSV file
# An argument containing exactly ~xxx is replaced by the value of field xxx from the CSV file
# Otherwise, the argument is preserved as is

SUB_PATTERN = re.compile(r'~~(.+?)~~')
RE_PATTERN = re.compile(r'~~(.+?)~!~(.+?)~!~(.+?)~~')
SUB_TYPE = u'sub'
RE_TYPE = u're'

# SubFields is a dictionary; the key is the argument number, the value is a list of tuples that mark
# the substition (type, fieldname, start, end). Type is 'sub' for simple substitution, 're' for regex substitution.
# Example: update user '~User' address type work unstructured '~~Street~~, ~~City~~, ~~State~~ ~~ZIP~~' primary
# {2: [('sub', 'User', 0, 5)], 7: [('sub', 'Street', 0, 10), ('sub', 'City', 12, 20), ('sub', 'State', 22, 31), ('sub', 'ZIP', 32, 39)]}
def getSubFields(initial_argv, fieldNames):
  global CL_argvI
  subFields = {}
  GAM_argv = initial_argv[:]
  GAM_argvI = len(GAM_argv)
  while CL_argvI < CL_argvLen:
    myarg = CL_argv[CL_argvI]
    if not myarg:
      GAM_argv.append(myarg)
    elif SUB_PATTERN.search(myarg):
      pos = 0
      subFields.setdefault(GAM_argvI, [])
      while True:
        submatch = SUB_PATTERN.search(myarg, pos)
        if not submatch:
          break
        rematch = RE_PATTERN.match(submatch.group(0))
        if not rematch:
          fieldName = submatch.group(1)
          if fieldName not in fieldNames:
            csvFieldErrorExit(fieldName, fieldNames)
          subFields[GAM_argvI].append((SUB_TYPE, fieldName, submatch.start(), submatch.end()))
        else:
          fieldName = rematch.group(1)
          if fieldName not in fieldNames:
            csvFieldErrorExit(fieldName, fieldNames)
          try:
            re.compile(rematch.group(2))
            subFields[GAM_argvI].append((RE_TYPE, fieldName, submatch.start(), submatch.end(), rematch.group(2), rematch.group(3)))
          except re.error as e:
            usageErrorExit(u'{0} {1}: {2}'.format(OB_RE_PATTERN, PHRASE_ERROR, e))
        pos = submatch.end()
      GAM_argv.append(myarg)
    elif myarg[0] == u'~':
      fieldName = myarg[1:]
      if fieldName in fieldNames:
        subFields[GAM_argvI] = [(SUB_TYPE, fieldName, 0, len(myarg))]
        GAM_argv.append(myarg)
      else:
        csvFieldErrorExit(fieldName, fieldNames)
    else:
      GAM_argv.append(myarg.encode(GM_Globals[GM_SYS_ENCODING]))
    GAM_argvI += 1
    CL_argvI += 1
  return(GAM_argv, subFields)

def processSubFields(GAM_argv, row, subFields):
  argv = GAM_argv[:]
  for GAM_argvI, fields in subFields.iteritems():
    oargv = argv[GAM_argvI][:]
    argv[GAM_argvI] = u''
    pos = 0
    for field in fields:
      argv[GAM_argvI] += oargv[pos:field[2]]
      if field[0] == SUB_TYPE:
        if row[field[1]]:
          argv[GAM_argvI] += row[field[1]]
      else:
        if row[field[1]]:
          argv[GAM_argvI] += re.sub(field[4], field[5], row[field[1]])
      pos = field[3]
    argv[GAM_argvI] += oargv[pos:]
    argv[GAM_argvI] = argv[GAM_argvI].encode(GM_Globals[GM_SYS_ENCODING])
  return argv

def doCSV():
  filename = getString(OB_FILE_NAME)
  if (filename == u'-') and (GC_Values[GC_DEBUG_LEVEL] > 0):
    putArgumentBack()
    usageErrorExit(MESSAGE_BATCH_CSV_DASH_DEBUG_INCOMPATIBLE.format(u'csv'))
  f, csvFile = openCSVFileReader(filename)
  matchFields = getMatchFields(csvFile.fieldnames)
  checkArgumentPresent([GAM_CMD,], required=True)
  if CL_argvI == CL_argvLen:
    missingArgumentExit(OB_GAM_ARGUMENT_LIST)
  GAM_argv, subFields = getSubFields([], csvFile.fieldnames)
  items = []
  for row in csvFile:
    if (not matchFields) or checkMatchFields(row, matchFields):
      items.append([GAM_CMD]+processSubFields(GAM_argv, row, subFields))
  closeFile(f)
  run_batch(items)

class cmd_flags(object):
  def __init__(self, noLocalWebserver):
    self.short_url = True
    self.noauth_local_webserver = noLocalWebserver
    self.logging_level = u'ERROR'
    self.auth_host_name = u'localhost'
    self.auth_host_port = [8080, 9090]

OAUTH2_SCOPES = [
  {u'name': u'Group Directory API',
   u'subscopes': [u'readonly'],
   u'scopes': u'https://www.googleapis.com/auth/admin.directory.group'},
  {u'name': u'Organizational Unit Directory API',
   u'subscopes': [u'readonly'],
   u'scopes': u'https://www.googleapis.com/auth/admin.directory.orgunit'},
  {u'name': u'Users Directory API',
   u'subscopes': [u'readonly'],
   u'scopes': u'https://www.googleapis.com/auth/admin.directory.user'},
  {u'name': u'Chrome OS Devices Directory API',
   u'subscopes': [u'readonly'],
   u'scopes': u'https://www.googleapis.com/auth/admin.directory.device.chromeos'},
  {u'name': u'Mobile Devices Directory API',
   u'subscopes': [u'readonly', u'action'],
   u'scopes': u'https://www.googleapis.com/auth/admin.directory.device.mobile'},
  {u'name': u'Legacy Email Settings API - Delegation',
   u'subscopes': [],
   u'scopes': u'https://apps-apis.google.com/a/feeds/emailsettings/2.0/'},
  {u'name': u'Resource Calendar API',
   u'subscopes': [u'readonly'],
   u'scopes': u'https://www.googleapis.com/auth/admin.directory.resource.calendar'},
  {u'name': u'Admin Settings API',
   u'offByDefault': True,
   u'subscopes': [],
   u'scopes': u'https://apps-apis.google.com/a/feeds/domain/'},
  {u'name': u'Audit Monitors, Activity and Mailbox Exports API',
   u'offByDefault': True,
   u'subscopes': [],
   u'scopes': u'https://apps-apis.google.com/a/feeds/compliance/audit/'},
  {u'name': u'Groups Settings API',
   u'subscopes': [],
   u'scopes': u'https://www.googleapis.com/auth/apps.groups.settings'},
  {u'name': u'Calendar Data API',
   u'subscopes': [u'readonly'],
   u'scopes': u'https://www.googleapis.com/auth/calendar'},
  {u'name': u'Audit Reports API',
   u'subscopes': [],
   u'scopes': u'https://www.googleapis.com/auth/admin.reports.audit.readonly'},
  {u'name': u'Usage Reports API',
   u'subscopes': [],
   u'scopes': u'https://www.googleapis.com/auth/admin.reports.usage.readonly'},
  {u'name': u'Drive API - create report docs only',
   u'subscopes': [],
   u'scopes': u'https://www.googleapis.com/auth/drive.file'},
  {u'name': u'License Manager API',
   u'subscopes': [],
   u'scopes': u'https://www.googleapis.com/auth/apps.licensing'},
  {u'name': u'User Security Directory API',
   u'subscopes': [],
   u'scopes': u'https://www.googleapis.com/auth/admin.directory.user.security'},
  {u'name': u'Notifications Directory API',
   u'subscopes': [],
   u'scopes': u'https://www.googleapis.com/auth/admin.directory.notifications'},
  {u'name': u'Site Verification API',
   u'offByDefault': True,
   u'subscopes': [],
   u'scopes': u'https://www.googleapis.com/auth/siteverification'},
  {u'name': u'Gmail API - send report docs todrive notifications only',
   u'subscopes': [],
   u'scopes': u'https://www.googleapis.com/auth/gmail.send'},
  {u'name': u'User Schema Directory API',
   u'subscopes': [u'readonly'],
   u'scopes': u'https://www.googleapis.com/auth/admin.directory.userschema'},
  {u'name': u'Classroom API - counts as 5 scopes',
   u'subscopes': [],
   u'scopes': [u'https://www.googleapis.com/auth/classroom.rosters',
               u'https://www.googleapis.com/auth/classroom.courses',
               u'https://www.googleapis.com/auth/classroom.profile.emails',
               u'https://www.googleapis.com/auth/classroom.profile.photos',
               u'https://www.googleapis.com/auth/classroom.guardianlinks.students']},
  {u'name': u'Cloud Print API',
   u'subscopes': [],
   u'scopes': u'https://www.googleapis.com/auth/cloudprint'},
  {u'name': u'Data Transfer API',
   u'subscopes': [u'readonly'],
   u'scopes': u'https://www.googleapis.com/auth/admin.datatransfer'},
  {u'name': u'Customer API',
   u'subscopes': [u'readonly'],
   u'scopes': u'https://www.googleapis.com/auth/admin.directory.customer'},
  {u'name': u'Domains Directory API',
   u'subscopes': [u'readonly'],
   u'scopes': u'https://www.googleapis.com/auth/admin.directory.domain'},
  {u'name': u'Roles Directory API',
   u'subscopes': [u'readonly'],
   u'scopes': u'https://www.googleapis.com/auth/admin.directory.rolemanagement'},
  ]

OAUTH2_CMDS = [u's', u'u', u'e', u'c']
MAXIMUM_SCOPES = 28

def doOAuthRequest(login_hint=None):
  def _checkMakeScopesList(scopes):
    del scopes[:]
    for i in range(num_scopes):
      if selected_scopes[i] == u'*':
        if not isinstance(OAUTH2_SCOPES[i][u'scopes'], list):
          scopes.append(OAUTH2_SCOPES[i][u'scopes'])
        else:
          scopes += OAUTH2_SCOPES[i][u'scopes']
      elif selected_scopes[i] == u'R':
        scopes.append(u'%s.readonly' % OAUTH2_SCOPES[i][u'scopes'])
      elif selected_scopes[i] == u'A':
        scopes.append(u'%s.action' % OAUTH2_SCOPES[i][u'scopes'])
    if len(scopes) > MAXIMUM_SCOPES:
      return (False, u'ERROR: {0} scopes selected, maximum is {1}, please unselect some.\n'.format(len(scopes), MAXIMUM_SCOPES))
    if len(scopes) == 0:
      return (False, u'ERROR: No scopes selected, please select at least one.\n')
    scopes.insert(0, u'email') # Email Display Scope, always included
    return (True, u'')

  MISSING_CLIENT_SECRETS_MESSAGE = u'''To use GAM you need to create an API project. Please run:

gam create project
'''

  cs_data = readFile(GC_Values[GC_CLIENT_SECRETS_JSON], mode=u'rb', continueOnError=True, displayError=True, encoding=None)
  if not cs_data:
    systemErrorExit(14, MISSING_CLIENT_SECRETS_MESSAGE)
  try:
    cs_json = json.loads(cs_data)
    client_id = cs_json[u'installed'][u'client_id']
    client_secret = cs_json[u'installed'][u'client_secret']
  except (ValueError, IndexError, KeyError):
    print u'ERROR: the format of your client secrets file:\n\n%s\n\n is incorrect. Please recreate the file.'
    sys.exit(3)

  checkForExtraneousArguments()
  login_hint = getValidateLoginHint(login_hint)
  oauth2_menu = u'''
Select the authorized scopes by entering a number.
Append an 'r' to grant read-only access or an 'a' to grant action-only access.

'''
  for a_scope in OAUTH2_SCOPES:
    oauth2_menu += u'[%%%%s] %%2d)  %s' % (a_scope[u'name'])
    if a_scope[u'subscopes']:
      oauth2_menu += u' (supports %s)' % (u' and '.join(a_scope[u'subscopes']))
    oauth2_menu += '\n'
  oauth2_menu += '''
     s)  Select all scopes
     u)  Unselect all scopes
     e)  Exit without changes
     c)  Continue to authorization
'''

  num_scopes = len(OAUTH2_SCOPES)
  menu = oauth2_menu % tuple(range(num_scopes))
  selected_scopes = []
  for scope in OAUTH2_SCOPES:
    if scope.get(u'offByDefault', False):
      selected_scopes.append(u' ')
    else:
      selected_scopes.append(u'*')
  scopes = []
  prompt = u'Please enter 0-{0}[a|r] or {1}: '.format(num_scopes-1, u'|'.join(OAUTH2_CMDS))
  message = u''
  while True:
    os.system([u'clear', u'cls'][GM_Globals[GM_WINDOWS]])
    if message:
      sys.stdout.write(message)
      message = u''
    sys.stdout.write(menu % tuple(selected_scopes))
    while True:
      choice = raw_input(prompt)
      if choice:
        selection = choice.lower()
        if selection.find(u'r') >= 0:
          mode = u'R'
          selection = selection.replace(u'r', u'')
        elif selection.find(u'a') >= 0:
          mode = u'A'
          selection = selection.replace(u'a', u'')
        else:
          mode = u' '
        if selection and selection.isdigit():
          selection = int(selection)
        if isinstance(selection, int) and selection < num_scopes:
          if mode == u'R':
            if u'readonly' not in OAUTH2_SCOPES[selection][u'subscopes']:
              sys.stdout.write(u'{0}Scope {1} does not support read-only mode!\n'.format(ERROR_PREFIX, selection))
              continue
          elif mode == u'A':
            if u'action' not in OAUTH2_SCOPES[selection][u'subscopes']:
              sys.stdout.write(u'{0}Scope {1} does not support action-only mode!\n'.format(ERROR_PREFIX, selection))
              continue
          elif selected_scopes[selection] != u'*':
            mode = u'*'
          else:
            mode = u' '
          selected_scopes[selection] = mode
          break
        elif isinstance(selection, str) and selection in OAUTH2_CMDS:
          if selection == u's':
            for i in range(num_scopes):
              selected_scopes[i] = u'*'
          elif selection == u'u':
            for i in range(num_scopes):
              selected_scopes[i] = u' '
          elif selection == u'e':
            return
          break
        sys.stdout.write(u'{0}Invalid input "{1}"\n'.format(ERROR_PREFIX, choice))
    if selection == u'c':
      status, message = _checkMakeScopesList(scopes)
      if status:
        break
  flow = oauth2client.client.OAuth2WebServerFlow(client_id=client_id,
                                                 client_secret=client_secret, scope=scopes, redirect_uri=oauth2client.client.OOB_CALLBACK_URN,
                                                 user_agent=GAM_INFO, access_type=u'offline', response_type=u'code', login_hint=login_hint)
  storage, _ = getOauth2TxtStorageCredentials()
  http = httplib2.Http(disable_ssl_certificate_validation=GC_Values[GC_NO_VERIFY_SSL])
  flags = cmd_flags(noLocalWebserver=GC_Values[GC_NO_BROWSER])
  try:
    oauth2client.tools.run_flow(flow=flow, storage=storage, flags=flags, http=http)
  except httplib2.CertificateValidationUnsupported:
    noPythonSSLExit()

def doOAuthDelete():
  checkForExtraneousArguments()
  _, credentials = getOauth2TxtStorageCredentials()
  if credentials is None or credentials.invalid:
    os.remove(GC_Values[GC_OAUTH2_TXT])
    return
  try:
    credentials.revoke_uri = oauth2client.GOOGLE_REVOKE_URI
  except AttributeError:
    systemErrorExit(1, u'Authorization doesn\'t exist')
  sys.stderr.write(u'This OAuth token will self-destruct in 3...')
  time.sleep(1)
  sys.stderr.write(u'2...')
  time.sleep(1)
  sys.stderr.write(u'1...')
  time.sleep(1)
  sys.stderr.write(u'boom!\n')
  try:
    credentials.revoke(httplib2.Http(disable_ssl_certificate_validation=GC_Values[GC_NO_VERIFY_SSL]))
  except oauth2client.client.TokenRevokeError as e:
    stderrErrorMsg(e.message)
    os.remove(GC_Values[GC_OAUTH2_TXT])

def doOAuthInfo():
  access_token = getString(OB_ACCESS_TOKEN, optional=True)
  checkForExtraneousArguments()
  if not access_token:
    storage, credentials = getOauth2TxtStorageCredentials()
    if credentials is None or credentials.invalid:
      doOAuthRequest()
      credentials = storage.get()
    credentials.user_agent = GAM_INFO
    http = httplib2.Http(disable_ssl_certificate_validation=GC_Values[GC_NO_VERIFY_SSL])
    if credentials.access_token_expired:
      credentials.refresh(http)
    access_token = credentials.access_token
    print u"\nOAuth File: %s" % GC_Values[GC_OAUTH2_TXT]
  oa2 = buildGAPIObject(GAPI_OAUTH2_API)
  token_info = callGAPI(oa2, u'tokeninfo', access_token=access_token)
  print u"Client ID: %s" % token_info[u'issued_to']
  try:
    print u"Secret: %s" % credentials.client_secret
  except UnboundLocalError:
    pass
  print u'Scopes:'
  for scope in token_info[u'scope'].split(u' '):
    print u'  %s' % scope
  try:
    print u'G Suite Admin: %s' % token_info[u'email']
  except KeyError:
    print u'G Suite Admin: Unknown'

def doWhatIs():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  email = getEmailAddress()
  show_info = not checkArgumentPresent(NOINFO_ARGUMENT)
  if not show_info:
    checkForExtraneousArguments()
  try:
    user_or_alias = callGAPI(cd.users(), u'get', throw_reasons=[GAPI_NOT_FOUND, GAPI_BAD_REQUEST, GAPI_INVALID], userKey=email, fields=u'primaryEmail')
    if user_or_alias[u'primaryEmail'].lower() == email.lower():
      sys.stderr.write(u'%s is a user\n\n' % email)
      if show_info:
        doInfoUser(user_email=email)
      return
    else:
      sys.stderr.write(u'%s is a user alias\n\n' % email)
      if show_info:
        doInfoAlias(alias_email=email)
      return
  except (GAPI_notFound, GAPI_badRequest, GAPI_invalid):
    sys.stderr.write(u'%s is not a user...\n' % email)
    sys.stderr.write(u'%s is not a user alias...\n' % email)
  try:
    group = callGAPI(cd.groups(), u'get', throw_reasons=[GAPI_NOT_FOUND, GAPI_BAD_REQUEST], groupKey=email, fields=u'email')
  except (GAPI_notFound, GAPI_badRequest):
    sys.stderr.write(u'%s is not a group either!\n\nDoesn\'t seem to exist!\n\n' % email)
    sys.exit(1)
  if group[u'email'].lower() == email.lower():
    sys.stderr.write(u'%s is a group\n\n' % email)
    if show_info:
      doInfoGroup(group_name=email)
  else:
    sys.stderr.write(u'%s is a group alias\n\n' % email)
    if show_info:
      doInfoAlias(alias_email=email)

def doCheckServiceAccount(users):
  all_scopes = []
  for _, scopes in API_SCOPE_MAPPING.items():
    for scope in scopes:
      if scope not in all_scopes:
        all_scopes.append(scope)
  all_scopes.sort()
  for user in users:
    all_scopes_pass = True
    print u'User: %s' % (user)
    for scope in all_scopes:
      try:
        credentials = getSvcAcctCredentials(scope, user)
        credentials.refresh(httplib2.Http(disable_ssl_certificate_validation=GC_Values[GC_NO_VERIFY_SSL]))
        result = u'PASS'
      except httplib2.ServerNotFoundError as e:
        systemErrorExit(4, e)
      except oauth2client.client.HttpAccessTokenRefreshError:
        result = u'FAIL'
        all_scopes_pass = False
      print u' Scope: {0:60} {1}'.format(scope, result)
    service_account = credentials.serialization_data[u'client_id']
    if all_scopes_pass:
      print u'\nAll scopes passed!\nService account %s is fully authorized.' % service_account
    else:
      _, user_domain = splitEmailAddress(user)
      print u'''
ERROR: Some scopes failed! Please go to:

https://admin.google.com/%s/AdminHome?#OGX:ManageOauthClients

and grant Client name:

%s

Access to scopes:

%s\n''' % (user_domain, service_account, ',\n'.join(all_scopes))
    sys.exit(int(not all_scopes_pass))

REPORT_CUSTOMER = u'customer'
REPORT_USER = u'user'

REPORT_CHOICES_MAP = {
  u'admin': u'admin',
  u'calendar': u'calendar',
  u'calendars': u'calendar',
  u'customer': u'customer',
  u'customers': u'customer',
  u'doc': u'drive',
  u'docs': u'drive',
  u'domain': u'customer',
  u'drive': u'drive',
  u'group': u'groups',
  u'groups': u'groups',
  u'login': u'login',
  u'logins': u'login',
  u'mobile': u'mobile',
  u'token': u'token',
  u'tokens': u'token',
  u'user': u'user',
  u'users': u'user',
  }

def showReport():

  def _adjustDate(errMsg):
    match_date = re.match(u'Data for dates later than (.*) is not yet available. Please check back later', errMsg)
    if not match_date:
      match_date = re.match(u'Start date can not be later than (.*)', errMsg)
    if not match_date:
      systemErrorExit(4, errMsg)
    return str(match_date.group(1))

  rep = buildGAPIObject(GAPI_REPORTS_API)
  report = getChoice(REPORT_CHOICES_MAP, mapChoice=True)
  customerId = GC_Values[GC_CUSTOMER_ID]
  if customerId == MY_CUSTOMER:
    customerId = None
  try_date = filters = parameters = actorIpAddress = startTime = endTime = eventName = None
  to_drive = False
  userKey = u'all'
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'date':
      try_date = getYYYYMMDD()
    elif myarg == u'start':
      startTime = getFullTime()
    elif myarg == u'end':
      endTime = getFullTime()
    elif myarg == u'event':
      eventName = getString(OB_STRING)
    elif myarg == u'user':
      userKey = getString(OB_EMAIL_ADDRESS)
    elif myarg in [u'filter', u'filters']:
      filters = getString(OB_STRING)
    elif myarg in [u'fields', u'parameters']:
      parameters = getString(OB_STRING)
    elif myarg == u'ip':
      actorIpAddress = getString(OB_STRING)
    elif myarg == u'todrive':
      to_drive = True
    else:
      unknownArgumentExit()
  if try_date is None:
    try_date = str(datetime.date.today())
  if report == REPORT_USER:
    while True:
      try:
        page_message = u'Got %%num_items%% users\n'
        feed = callGAPIpages(rep.userUsageReport(), u'get', u'usageReports', page_message=page_message, throw_reasons=[GAPI_INVALID],
                             date=try_date, userKey=userKey, customerId=customerId, filters=filters, parameters=parameters)
        break
      except GAPI_invalid as e:
        error = json.loads(e.content)
      try:
        message = error[u'error'][u'errors'][0][u'message']
      except KeyError:
        raise
      try_date = _adjustDate(message)
    titles = [u'email', u'date']
    csvRows = []
    while feed:
      user_report = feed.popleft()
      row = {u'email': user_report[u'entity'][u'userEmail'], u'date': try_date}
      try:
        for report_item in user_report[u'parameters']:
          items = report_item.values()
          name = items[1]
          value = items[0]
          if not name in titles:
            titles.append(name)
          row[name] = value
      except KeyError:
        pass
      csvRows.append(row)
    writeCSVfile(csvRows, titles, u'User Reports - %s' % try_date, to_drive)
  elif report == REPORT_CUSTOMER:
    while True:
      try:
        usage = callGAPIpages(rep.customerUsageReports(), u'get', u'usageReports', throw_reasons=[GAPI_INVALID],
                              customerId=customerId, date=try_date, parameters=parameters)
        break
      except GAPI_invalid as e:
        error = json.loads(e.content)
      try:
        message = error[u'error'][u'errors'][0][u'message']
      except KeyError:
        raise
      try_date = _adjustDate(message)
    titles = [u'name', u'value', u'client_id']
    csvRows = []
    auth_apps = []
    for item in usage[0][u'parameters']:
      name = item[u'name']
      try:
        value = item[u'intValue']
      except KeyError:
        if name == u'accounts:authorized_apps':
          for subitem in item[u'msgValue']:
            app = {}
            for an_item in subitem:
              if an_item == u'client_name':
                app[u'name'] = u'App: %s' % subitem[an_item]
              elif an_item == u'num_users':
                app[u'value'] = u'%s users' % subitem[an_item]
              elif an_item == u'client_id':
                app[u'client_id'] = subitem[an_item]
            auth_apps.append(app)
        continue
      csvRows.append({u'name': name, u'value': value})
    for row in auth_apps: # put apps at bottom
      csvRows.append(row)
    writeCSVfile(csvRows, titles, u'Customer Report - %s' % try_date, todrive=to_drive)
  else:
    page_message = u'Got %%num_items%% items\n'
    feed = callGAPIpages(rep.activities(), u'list', u'items', page_message=page_message, applicationName=report,
                         userKey=userKey, customerId=customerId, actorIpAddress=actorIpAddress,
                         startTime=startTime, endTime=endTime, eventName=eventName, filters=filters)
    if feed:
      titles = [u'name']
      csvRows = []
      while feed:
        activity = feed.popleft()
        events = activity[u'events']
        del activity[u'events']
        activity_row = flattenJSON(activity)
        for event in events:
          row = flattenJSON(event)
          row.update(activity_row)
          for item in row:
            if item not in titles:
              titles.append(item)
          csvRows.append(row)
      sortCSVTitles([u'name',], titles)
      writeCSVfile(csvRows, titles, u'%s Activity Report' % report.capitalize(), to_drive)

def doCreateDomainAlias():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  body = {u'domainAliasName': getString(OB_DOMAIN_ALIAS)}
  body[u'parentDomainName'] = getString(OB_DOMAIN_NAME)
  checkForExtraneousArguments()
  callGAPI(cd.domainAliases(), u'insert', customer=GC_Values[GC_CUSTOMER_ID], body=body)

def doDeleteDomainAlias():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  domainAliasName = getString(OB_DOMAIN_ALIAS)
  checkForExtraneousArguments()
  callGAPI(cd.domainAliases(), u'delete', customer=GC_Values[GC_CUSTOMER_ID], domainAliasName=domainAliasName)

def doInfoDomainAlias():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  domainAliasName = getString(OB_DOMAIN_ALIAS)
  checkForExtraneousArguments()
  result = callGAPI(cd.domainAliases(), u'get', customer=GC_Values[GC_CUSTOMER_ID], domainAliasName=domainAliasName)
  if u'creationTime' in result:
    result[u'creationTime'] = unicode(datetime.datetime.fromtimestamp(int(result[u'creationTime'])/1000))
  showJSON(None, result)

def doPrintDomainAliases():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  todrive = False
  titles = [u'domainAliasName',]
  csvRows = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  results = callGAPI(cd.domainAliases(), u'list', customer=GC_Values[GC_CUSTOMER_ID])
  for domainAlias in results[u'domainAliases']:
    row = {}
    for attr in domainAlias:
      if attr in [u'kind', u'etag']:
        continue
      if attr == u'creationTime':
        domainAlias[attr] = unicode(datetime.datetime.fromtimestamp(int(domainAlias[attr])/1000))
      if attr not in titles:
        titles.append(attr)
      row[attr] = domainAlias[attr]
    csvRows.append(row)
  writeCSVfile(csvRows, titles, u'Domains', todrive)

def doCreateDomain():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  body = {u'domainName': getString(OB_DOMAIN_NAME)}
  checkForExtraneousArguments()
  callGAPI(cd.domains(), u'insert', customer=GC_Values[GC_CUSTOMER_ID], body=body)
  print u'Added domain %s' % body[u'domainName']

def doUpdateDomain():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  domainName = getString(OB_DOMAIN_NAME)
  body = {}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'primary':
      body[u'customerDomain'] = domainName
    else:
      unknownArgumentExit()
  callGAPI(cd.customers(), u'update', customerKey=GC_Values[GC_CUSTOMER_ID], body=body)
  print u'%s is now the primary domain.' % domainName

def doDeleteDomain():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  domainName = getString(OB_DOMAIN_NAME)
  checkForExtraneousArguments()
  callGAPI(cd.domains(), u'delete', customer=GC_Values[GC_CUSTOMER_ID], domainName=domainName)

def doInfoDomain():
  if (CL_argvI == CL_argvLen) or (CL_argv[CL_argvI].lower() == u'logo'):
    doInfoCustomer()
    return
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  domainName = getString(OB_DOMAIN_NAME)
  checkForExtraneousArguments()
  result = callGAPI(cd.domains(), u'get', customer=GC_Values[GC_CUSTOMER_ID], domainName=domainName)
  if u'creationTime' in result:
    result[u'creationTime'] = unicode(datetime.datetime.fromtimestamp(int(result[u'creationTime'])/1000))
  if u'domainAliases' in result:
    for i in range(len(result[u'domainAliases'])):
      if u'creationTime' in result[u'domainAliases'][i]:
        result[u'domainAliases'][i][u'creationTime'] = unicode(datetime.datetime.fromtimestamp(int(result[u'domainAliases'][i][u'creationTime'])/1000))
  showJSON(None, result)

def doPrintDomains():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  todrive = False
  titles = [u'domainName',]
  csvRows = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  results = callGAPI(cd.domains(), u'list', customer=GC_Values[GC_CUSTOMER_ID])
  for domain in results[u'domains']:
    row = {}
    domain[u'type'] = [u'secondary', u'primary'][domain[u'isPrimary']]
    for attr in domain:
      if attr in [u'kind', u'etag', u'domainAliases', u'isPrimary']:
        continue
      if attr in [u'creationTime',]:
        domain[attr] = unicode(datetime.datetime.fromtimestamp(int(domain[attr])/1000))
      if attr not in titles:
        titles.append(attr)
      row[attr] = domain[attr]
    csvRows.append(row)
    if u'domainAliases' in domain:
      for aliasdomain in domain[u'domainAliases']:
        aliasdomain[u'domainName'] = aliasdomain[u'domainAliasName']
        del aliasdomain[u'domainAliasName']
        aliasdomain[u'type'] = u'alias'
        row = {}
        for attr in aliasdomain:
          if attr in [u'kind', u'etag']:
            continue
          if attr in [u'creationTime',]:
            aliasdomain[attr] = unicode(datetime.datetime.fromtimestamp(int(aliasdomain[attr])/1000))
          if attr not in titles:
            titles.append(attr)
          row[attr] = aliasdomain[attr]
        csvRows.append(row)
  writeCSVfile(csvRows, titles, u'Domains', todrive)

def doPrintAdminRoles():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  todrive = False
  titles = [u'roleId', u'roleName', u'roleDescription', u'isSuperAdminRole', u'isSystemRole']
  fields = u'nextPageToken,items({0})'.format(u','.join(titles))
  csvRows = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  roles = callGAPIpages(cd.roles(), u'list', u'items',
                        customer=GC_Values[GC_CUSTOMER_ID], fields=fields)
  for role in roles:
    row = {}
    for key, value in role.items():
      row[key] = value
    csvRows.append(row)
  writeCSVfile(csvRows, titles, u'Admin Roles', todrive)

def buildOrgUnitIdToNameMap():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  result = callGAPI(cd.orgunits(), u'list',
                    customerId=GC_Values[GC_CUSTOMER_ID],
                    fields=u'organizationUnits(orgUnitPath,orgUnitId)', type=u'all')
  GM_Globals[GM_MAP_ORGUNIT_ID_TO_NAME] = {}
  for orgUnit in result[u'organizationUnits']:
    GM_Globals[GM_MAP_ORGUNIT_ID_TO_NAME][orgUnit[u'orgUnitId']] = orgUnit[u'orgUnitPath']

def orgunit_from_orgunitid(orgunitid):
  if not GM_Globals[GM_MAP_ORGUNIT_ID_TO_NAME]:
    buildOrgUnitIdToNameMap()
  return GM_Globals[GM_MAP_ORGUNIT_ID_TO_NAME].get(orgunitid, orgunitid)

def buildRoleIdToNameToIdMap():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  result = callGAPIpages(cd.roles(), u'list', u'items',
                         customer=GC_Values[GC_CUSTOMER_ID],
                         fields=u'nextPageToken,items(roleId,roleName)',
                         maxResults=100)
  GM_Globals[GM_MAP_ROLE_ID_TO_NAME] = {}
  GM_Globals[GM_MAP_ROLE_NAME_TO_ID] = {}
  for role in result:
    GM_Globals[GM_MAP_ROLE_ID_TO_NAME][role[u'roleId']] = role[u'roleName']
    GM_Globals[GM_MAP_ROLE_NAME_TO_ID][role[u'roleName']] = role[u'roleId']

def role_from_roleid(roleid):
  if not GM_Globals[GM_MAP_ROLE_ID_TO_NAME]:
    buildRoleIdToNameToIdMap()
  return GM_Globals[GM_MAP_ROLE_ID_TO_NAME].get(roleid, roleid)

def roleid_from_role(role):
  if not GM_Globals[GM_MAP_ROLE_NAME_TO_ID]:
    buildRoleIdToNameToIdMap()
  return GM_Globals[GM_MAP_ROLE_NAME_TO_ID].get(role, None)

def buildUserIdToNameMap():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  result = callGAPIpages(cd.users(), u'list', u'users',
                         customer=GC_Values[GC_CUSTOMER_ID],
                         fields=u'nextPageToken,users(id,primaryEmail)',
                         maxResults=GC_Values[GC_USER_MAX_RESULTS])
  GM_Globals[GM_MAP_USER_ID_TO_NAME] = {}
  for user in result:
    GM_Globals[GM_MAP_USER_ID_TO_NAME][user[u'id']] = user[u'primaryEmail']

def user_from_userid(userid):
  if not GM_Globals[GM_MAP_USER_ID_TO_NAME]:
    buildUserIdToNameMap()
  return GM_Globals[GM_MAP_USER_ID_TO_NAME].get(userid, u'')

def getRoleId():
  role = getString(OB_ROLE_ID)
  if role[:4].lower() == u'uid:':
    roleId = role[4:]
  else:
    roleId = roleid_from_role(role)
    if not roleId:
      putArgumentBack()
      invalidChoiceExit(GM_Globals[GM_MAP_ROLE_NAME_TO_ID])
  return (role, roleId)

def getOrgUnitId(cd):
  orgUnit = getOrgUnitPath()
  if orgUnit[:3] == u'id:':
    return (orgUnit, orgUnit[3:])
  try:
    result = callGAPI(cd.orgunits(), u'get',
                      throw_reasons=[GAPI_INVALID_ORGUNIT, GAPI_ORGUNIT_NOT_FOUND, GAPI_BACKEND_ERROR],
                      customerId=GC_Values[GC_CUSTOMER_ID], orgUnitPath=makeOrgUnitPathRelative(orgUnit),
                      fields=u'orgUnitId')
    return (orgUnit, result[u'orgUnitId'][3:])
  except (GAPI_invalidOrgunit, GAPI_orgunitNotFound, GAPI_backendError):
    putArgumentBack()
    usageErrorExit(u'Organizational Unit: {0}, Does not exist'.format(orgUnit))

ADMIN_SCOPE_TYPE_CHOICE_MAP = {
  u'customer': u'CUSTOMER',
  u'orgunit': u'ORG_UNIT',
  }

def doCreateAdmin():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  user = getEmailAddress()
  body = {u'assignedTo': convertEmailToUserID(user)}
  role, roleId = getRoleId()
  body[u'roleId'] = roleId
  body[u'scopeType'] = getChoice(ADMIN_SCOPE_TYPE_CHOICE_MAP, mapChoice=True)
  if body[u'scopeType'] == u'ORG_UNIT':
    orgUnit, body[u'orgUnitId'] = getOrgUnitId(cd)
    scope = orgUnit
  else:
    scope = u'customer'
  checkForExtraneousArguments()
  print u'Giving %s admin role %s for %s' % (user, role, scope)
  callGAPI(cd.roleAssignments(), u'insert',
           customer=GC_Values[GC_CUSTOMER_ID], body=body)

def doDeleteAdmin():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  roleAssignmentId = getString(OB_ROLE_ASSIGNMENT_ID)
  checkForExtraneousArguments()
  print u'Deleting Admin Role Assignment %s' % roleAssignmentId
  callGAPI(cd.roleAssignments(), u'delete',
           customer=GC_Values[GC_CUSTOMER_ID], roleAssignmentId=roleAssignmentId)

def doPrintAdmins():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  roleId = None
  userKey = None
  todrive = False
  fields = u'nextPageToken,items({0})'.format(u','.join([u'roleAssignmentId', u'roleId', u'assignedTo', u'scopeType', u'orgUnitId']))
  titles = [u'roleAssignmentId', u'roleId', u'role', u'assignedTo', u'assignedToUser', u'scopeType', u'orgUnitId', u'orgUnit']
  csvRows = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'user':
      userKey = getEmailAddress()
    elif myarg == u'role':
      _, roleId = getRoleId()
    elif myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  feed = callGAPIpages(cd.roleAssignments(), u'list', u'items',
                       customer=GC_Values[GC_CUSTOMER_ID], userKey=userKey, roleId=roleId, fields=fields)
  while feed:
    admin = feed.popleft()
    row = {}
    for key, value in admin.items():
      if key == u'assignedTo':
        row[u'assignedToUser'] = user_from_userid(value)
      elif key == u'roleId':
        row[u'role'] = role_from_roleid(value)
      elif key == u'orgUnitId':
        value = u'id:{0}'.format(value)
        row[u'orgUnit'] = orgunit_from_orgunitid(value)
      row[key] = value
    csvRows.append(row)
  writeCSVfile(csvRows, titles, u'Admins', todrive)

ADDRESS_FIELDS_PRINT_ORDER = [u'contactName', u'organizationName', u'addressLine1', u'addressLine2', u'addressLine3', u'locality', u'region', u'postalCode', u'countryCode']

def doInfoCustomer():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  customer_info = callGAPI(cd.customers(), u'get', customerKey=GC_Values[GC_CUSTOMER_ID])
  print u'Customer ID: %s' % customer_info[u'id']
  print u'Primary Domain: %s' % customer_info[u'customerDomain']
  result = callGAPI(cd.domains(), u'get',
                    customer=customer_info[u'id'], domainName=customer_info[u'customerDomain'], fields=u'verified')
  print u'Primary Domain Verified: %s' % result[u'verified']
  print u'Customer Creation Time: %s' % customer_info[u'customerCreationTime']
  print u'Default Language: %s' % customer_info[u'language']
  if u'postalAddress' in customer_info:
    print u'Address:'
    for field in ADDRESS_FIELDS_PRINT_ORDER:
      if field in customer_info[u'postalAddress']:
        print u' %s: %s' % (field, customer_info[u'postalAddress'][field])
  if u'phoneNumber' in customer_info:
    print u'Phone: %s' % customer_info[u'phoneNumber']
  print u'Admin Secondary Email: %s' % customer_info[u'alternateEmail']

ADDRESS_FIELDS_ARGUMENT_MAP = {
  u'contact': u'contactName', u'contactname': u'contactName',
  u'name': u'organizationName', u'organizationname': u'organizationName',
  u'address1': u'addressLine1', u'addressline1': u'addressLine1',
  u'address2': u'addressLine2', u'addressline2': u'addressLine2',
  u'address3': u'addressLine3', u'addressline3': u'addressLine3',
  u'locality': u'locality',
  u'region': u'region',
  u'postalcode': u'postalCode',
  u'country': u'countryCode', u'countrycode': u'countryCode',
  }

def doUpdateCustomer():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  body = {}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg in ADDRESS_FIELDS_ARGUMENT_MAP:
      body.setdefault(u'postalAddress', {})
      body[u'postalAddress'][ADDRESS_FIELDS_ARGUMENT_MAP[myarg]] = getString(OB_STRING, minLen=0)
    elif myarg in [u'adminsecondaryemail', u'alternateemail']:
      body[u'alternateEmail'] = getEmailAddress(noUid=True)
    elif myarg in [u'phone', u'phonenumber']:
      body[u'phoneNumber'] = getString(OB_STRING)
    elif myarg == u'language':
      body[u'language'] = getChoice(LANGUAGE_CODES_MAP, mapChoice=True)
    else:
      unknownArgumentExit()
  if body:
    callGAPI(cd.customers(), u'update', customerKey=GC_Values[GC_CUSTOMER_ID], body=body)
  print u'Updated customer'

SERVICE_NAME_TO_ID_MAP = {u'Drive and Docs': u'55656082996', u'Google+': u'553547912911',}

def appID2app(dt, appID):
  for serviceName, serviceID in SERVICE_NAME_TO_ID_MAP.items():
    if appID == serviceID:
      return serviceName
  online_services = callGAPIpages(dt.applications(), u'list', u'applications', customerId=GC_Values[GC_CUSTOMER_ID])
  for online_service in online_services:
    if appID == online_service[u'id']:
      return online_service[u'name']
  return u'applicationId: {0}'.format(appID)

SERVICE_NAME_CHOICES_MAP = {
  u'drive': u'Drive and Docs',
  u'drive and docs': u'Drive and Docs',
  u'googledrive': u'Drive and Docs',
  u'gdrive': u'Drive and Docs',
  }

def getService(dt):
  serviceName = getString(OB_SERVICE_NAME).lower()
  if serviceName in SERVICE_NAME_CHOICES_MAP:
    return (SERVICE_NAME_CHOICES_MAP[serviceName], SERVICE_NAME_TO_ID_MAP[SERVICE_NAME_CHOICES_MAP[serviceName]])
  online_services = callGAPIpages(dt.applications(), u'list', u'applications',
                                  customerId=GC_Values[GC_CUSTOMER_ID])
  serviceNameList = []
  for online_service in online_services:
    olServiceName = online_service[u'name']
    if olServiceName:
      if serviceName == olServiceName.lower():
        return (olServiceName, online_service[u'id'])
      serviceNameList.append(olServiceName.lower())
  putArgumentBack()
  invalidChoiceExit(serviceNameList)

def doCreateDataTranfer():
  dt = buildGAPIObject(GAPI_DATATRANSFER_API)
  old_owner = getEmailAddress()
  body = {u'oldOwnerUserId':  convertEmailToUserID(old_owner)}
  serviceName, serviceID = getService(dt)
  new_owner = getEmailAddress()
  body[u'newOwnerUserId'] = convertEmailToUserID(new_owner)
  if body[u'oldOwnerUserId'] == body[u'newOwnerUserId']:
    putArgumentBack()
    usageErrorExit(PHRASE_NEW_OWNER_MUST_DIFFER_FROM_OLD_OWNER)
  parameters = {}
  while CL_argvI < CL_argvLen:
    key = getString(OB_PARAMETER_KEY).upper()
    parameters[key] = getString(OB_PARAMETER_VALUE).upper().split(u',')
  body[u'applicationDataTransfers'] = [{u'applicationId': serviceID}]
  for key in parameters:
    if u'applicationDataTransferParams' not in body[u'applicationDataTransfers'][0]:
      body[u'applicationDataTransfers'][0][u'applicationTransferParams'] = []
    body[u'applicationDataTransfers'][0][u'applicationTransferParams'].append({u'key': key, u'value': parameters[key]})
  result = callGAPI(dt.transfers(), u'insert', body=body, fields=u'id')
  print u'Submitted request id %s to transfer %s from %s to %s' % (result[u'id'], serviceName, old_owner, new_owner)

def doInfoDataTransfer():
  dt = buildGAPIObject(GAPI_DATATRANSFER_API)
  dtId = getString(OB_TRANSFER_ID)
  checkForExtraneousArguments()
  transfer = callGAPI(dt.transfers(), u'get', dataTransferId=dtId)
  print u'Old Owner: %s' % convertUserIDtoEmail(transfer[u'oldOwnerUserId'])
  print u'New Owner: %s' % convertUserIDtoEmail(transfer[u'newOwnerUserId'])
  print u'Request Time: %s' % transfer[u'requestTime']
  for app in transfer[u'applicationDataTransfers']:
    print u'Application: %s' % appID2app(dt, app[u'applicationId'])
    print u'Status: %s' % app[u'applicationTransferStatus']
    print u'Parameters:'
    if u'applicationTransferParams' in app:
      for param in app[u'applicationTransferParams']:
        print   u' %s: %s' % (param[u'key'], u','.join(param[u'value']))
    else:
      print u' None'
    print

DATA_TRANSFER_STATUS_MAP = {
  u'completed': u'completed',
  u'failed': u'failed',
  u'pending': u'pending',
  u'inprogress': u'inProgress',
  }

def doPrintDataTransfers():
  dt = buildGAPIObject(GAPI_DATATRANSFER_API)
  newOwnerUserId = None
  oldOwnerUserId = None
  status = None
  todrive = False
  titles = [u'id',]
  csvRows = []
  delimiter = GC_Values[GC_CSV_OUTPUT_FIELD_DELIMITER]
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'todrive':
      todrive = True
    elif myarg in [u'olduser', u'oldowner']:
      oldOwnerUserId = convertEmailToUserID(getEmailAddress())
    elif myarg in [u'newuser', u'newowner']:
      newOwnerUserId = convertEmailToUserID(getEmailAddress())
    elif myarg == u'status':
      status = getChoice(DATA_TRANSFER_STATUS_MAP, mapChoice=True)
    elif myarg == u'delimiter':
      delimiter = getString(OB_STRING, minLen=1, maxLen=1)
    else:
      unknownArgumentExit()
  transfers = callGAPIpages(dt.transfers(), u'list', u'dataTransfers',
                            customerId=GC_Values[GC_CUSTOMER_ID], status=status,
                            newOwnerUserId=newOwnerUserId, oldOwnerUserId=oldOwnerUserId)
  for transfer in transfers:
    for i in range(len(transfer[u'applicationDataTransfers'])):
      row = {}
      row[u'oldOwnerUserEmail'] = convertUserIDtoEmail(transfer[u'oldOwnerUserId'])
      row[u'newOwnerUserEmail'] = convertUserIDtoEmail(transfer[u'newOwnerUserId'])
      row[u'requestTime'] = transfer[u'requestTime']
      row[u'applicationId'] = transfer[u'applicationDataTransfers'][i][u'applicationId']
      row[u'application'] = appID2app(dt, row[u'applicationId'])
      row[u'status'] = transfer[u'applicationDataTransfers'][i][u'applicationTransferStatus']
      row[u'id'] = transfer[u'id']
      if u'applicationTransferParams' in transfer[u'applicationDataTransfers'][i]:
        for param in transfer[u'applicationDataTransfers'][i][u'applicationTransferParams']:
          row[param[u'key']] = delimiter.join(param[u'value'])
    for title in row:
      if title not in titles:
        titles.append(title)
    csvRows.append(row)
  writeCSVfile(csvRows, titles, u'Data Transfers', todrive)

def doPrintTransferApps():
  dt = buildGAPIObject(GAPI_DATATRANSFER_API)
  checkForExtraneousArguments()
  apps = callGAPIpages(dt.applications(), u'list', u'applications', customerId=GC_Values[GC_CUSTOMER_ID])
  for app in apps:
    showJSON(None, app)
    print

UPDATE_INSTANCE_CHOICES = [u'logo', u'ssokey', u'ssosettings',]

def doUpdateInstance():
  adminObj = getAdminSettingsObject()
  command = getChoice(UPDATE_INSTANCE_CHOICES)
  if command == u'logo':
    logoFile = getString(OB_FILE_NAME)
    checkForExtraneousArguments()
    logoImage = readFile(logoFile)
    callGData(adminObj, u'UpdateDomainLogo', logoImage=logoImage)
  elif command == u'ssosettings':
    enableSSO = samlSignonUri = samlLogoutUri = changePasswordUri = ssoWhitelist = useDomainSpecificIssuer = None
    while CL_argvI < CL_argvLen:
      myarg = getArgument()
      if myarg == u'enabled':
        enableSSO = getBoolean()
      elif myarg == u'signonuri':
        samlSignonUri = getString(OB_URI)
      elif myarg == u'signouturi':
        samlLogoutUri = getString(OB_URI)
      elif myarg == u'passworduri':
        changePasswordUri = getString(OB_URI)
      elif myarg == u'whitelist':
        ssoWhitelist = getString(OB_CIDR_NETMASK)
      elif myarg == u'usedomainspecificissuer':
        useDomainSpecificIssuer = getBoolean()
      else:
        unknownArgumentExit()
    callGData(adminObj, u'UpdateSSOSettings', enableSSO=enableSSO,
              samlSignonUri=samlSignonUri, samlLogoutUri=samlLogoutUri,
              changePasswordUri=changePasswordUri, ssoWhitelist=ssoWhitelist,
              useDomainSpecificIssuer=useDomainSpecificIssuer)
  elif command == u'ssokey':
    keyFile = getString(OB_FILE_NAME)
    checkForExtraneousArguments()
    keyData = readFile(keyFile)
    callGData(adminObj, u'UpdateSSOKey', signingKey=keyData)

MAXIMUM_USERS_MAP = [u'maximumNumberOfUsers', u'Maximum Users']
CURRENT_USERS_MAP = [u'currentNumberOfUsers', u'Current Users']
DOMAIN_EDITION_MAP = [u'edition', u'Domain Edition']
CUSTOMER_PIN_MAP = [u'customerPIN', u'Customer PIN']
SINGLE_SIGN_ON_SETTINGS_MAP = [u'enableSSO', u'SSO Enabled',
                               u'samlSignonUri', u'SSO Signon Page',
                               u'samlLogoutUri', u'SSO Logout Page',
                               u'changePasswordUri', u'SSO Password Page',
                               u'ssoWhitelist', u'SSO Whitelist IPs',
                               u'useDomainSpecificIssuer', u'SSO Use Domain Specific Issuer']
SINGLE_SIGN_ON_SIGNING_KEY_MAP = [u'algorithm', u'SSO Key Algorithm',
                                  u'format', u'SSO Key Format',
                                  u'modulus', u'SSO Key Modulus',
                                  u'exponent', u'SSO Key Exponent',
                                  u'yValue', u'SSO Key yValue',
                                  u'signingKey', u'Full SSO Key']

def doInfoInstance():
  def _printAdminSetting(service, propertyTitleMap):
    try:
      result = callGAPI(service, u'get',
                        throw_reasons=[GAPI_DOMAIN_NOT_FOUND, GAPI_INVALID],
                        domainName=GC_Values[GC_DOMAIN])
      if result and (u'entry' in result) and (u'apps$property' in result[u'entry']):
        for i in range(0, len(propertyTitleMap), 2):
          asProperty = propertyTitleMap[i]
          for entry in result[u'entry'][u'apps$property']:
            if entry[u'name'] == asProperty:
              printKeyValueList(u'', [propertyTitleMap[i+1], entry[u'value']])
              break
    except GAPI_domainNotFound:
      systemErrorExit(INVALID_DOMAIN_RC, formatKeyValueList(u'', [u'Domain', GC_Values[GC_DOMAIN], PHRASE_DOES_NOT_EXIST], u''))
    except GAPI_invalid:
      pass

  if checkArgumentPresent(LOGO_ARGUMENT):
    target_file = getString(OB_FILE_NAME)
    checkForExtraneousArguments()
    url = u'http://www.google.com/a/cpanel/%s/images/logo.gif' % (GC_Values[GC_DOMAIN])
    geturl(url, target_file)
    return
  checkForExtraneousArguments()
  doInfoCustomer()
  adm = buildGAPIObject(GAPI_ADMIN_SETTINGS_API)
  _printAdminSetting(adm.maximumNumberOfUsers(), MAXIMUM_USERS_MAP)
  _printAdminSetting(adm.currentNumberOfUsers(), CURRENT_USERS_MAP)
  _printAdminSetting(adm.edition(), DOMAIN_EDITION_MAP)
  _printAdminSetting(adm.customerPIN(), CUSTOMER_PIN_MAP)
  _printAdminSetting(adm.ssoGeneral(), SINGLE_SIGN_ON_SETTINGS_MAP)
  _printAdminSetting(adm.ssoSigningKey(), SINGLE_SIGN_ON_SIGNING_KEY_MAP)

def doCreateOrg():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  name = getOrgUnitPath(absolutePath=False)
  body = {u'parentOrgUnitPath': u'/'}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'description':
      body[u'description'] = getString(OB_STRING)
    elif myarg == u'parent':
      parent = getOrgUnitPath()
    elif myarg == u'noinherit':
      body[u'blockInheritance'] = True
    elif myarg == u'inherit':
      body[u'blockInheritance'] = False
    else:
      unknownArgumentExit()
  if parent.startswith(u'id:'):
    body[u'parentOrgUnitId'] = parent
    body[u'name'] = name
    orgUnitPath = parent+u'/'+name
  else:
    if parent == u'/':
      orgUnitPath = parent+name
    else:
      orgUnitPath = parent+u'/'+name
    if orgUnitPath.count(u'/') > 1:
      body[u'parentOrgUnitPath'], body[u'name'] = orgUnitPath.rsplit(u'/', 1)
    else:
      body[u'parentOrgUnitPath'] = u'/'
      body[u'name'] = orgUnitPath[1:]
    parent = body[u'parentOrgUnitPath']
  callGAPI(cd.orgunits(), u'insert', customerId=GC_Values[GC_CUSTOMER_ID], body=body)

def doUpdateOrg():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  orgUnitPath = getOrgUnitPath()
  if checkArgumentPresent(MOVE_ADD_ARGUMENT):
    entityType, entityList = getEntityToModify(crosAllowed=True)
    checkForExtraneousArguments()
    i = 0
    count = len(entityList)
    if entityType == u'users':
      for user in entityList:
        i += 1
        user = normalizeEmailAddressOrUID(user)
        sys.stderr.write(u' moving %s to %s%s\n' % (user, orgUnitPath, currentCount(i, count)))
        try:
          callGAPI(cd.users(), u'patch', throw_reasons=[GAPI_CONDITION_NOT_MET], userKey=user, body={u'orgUnitPath': orgUnitPath})
        except GAPI_conditionNotMet:
          pass
    else:
      for cros in entityList:
        i += 1
        sys.stderr.write(u' moving %s to %s%s\n' % (cros, orgUnitPath, currentCount(i, count)))
        callGAPI(cd.chromeosdevices(), u'patch', soft_errors=True,
                 customerId=GC_Values[GC_CUSTOMER_ID], deviceId=cros, body={u'orgUnitPath': orgUnitPath})
  else:
    body = {}
    while CL_argvI < CL_argvLen:
      myarg = getArgument()
      if myarg == u'name':
        body[u'name'] = getString(OB_STRING)
      elif myarg == u'description':
        body[u'description'] = getString(OB_STRING)
      elif myarg == u'parent':
        parent = getOrgUnitPath()
        if parent.startswith(u'id:'):
          body[u'parentOrgUnitId'] = parent
        else:
          body[u'parentOrgUnitPath'] = parent
      elif myarg == u'noinherit':
        body[u'blockInheritance'] = True
      elif myarg == u'inherit':
        body[u'blockInheritance'] = False
      else:
        unknownArgumentExit()
    if orgUnitPath[0] == u'/': # we don't want a / at the beginning for OU updates
      orgUnitPath = orgUnitPath[1:]
    callGAPI(cd.orgunits(), u'update', customerId=GC_Values[GC_CUSTOMER_ID], orgUnitPath=orgUnitPath, body=body)

def doDeleteOrg():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  orgUnitPath = getOrgUnitPath(absolutePath=False)
  checkForExtraneousArguments()
  print u"Deleting organization %s" % orgUnitPath
  callGAPI(cd.orgunits(), u'delete', customerId=GC_Values[GC_CUSTOMER_ID], orgUnitPath=orgUnitPath)

def doInfoOrg():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  name = getOrgUnitPath()
  get_users = True
  show_children = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'nousers':
      get_users = False
    elif myarg in [u'children', u'child']:
      show_children = True
    else:
      unknownArgumentExit()
  if name == u'/':
    orgs = callGAPI(cd.orgunits(), u'list',
                    customerId=GC_Values[GC_CUSTOMER_ID], type=u'children',
                    fields=u'organizationUnits/parentOrgUnitId')
    name = orgs[u'organizationUnits'][0][u'parentOrgUnitId']
  if len(name) > 1 and name[0] == u'/':
    name = name[1:]
  result = callGAPI(cd.orgunits(), u'get', customerId=GC_Values[GC_CUSTOMER_ID], orgUnitPath=name)
  showJSON(None, result)
  if get_users:
    name = result[u'orgUnitPath']
    print u'Users: '
    page_message = u'Got %%total_items%% users: %%first_item%% - %%last_item%%\n'
    users = callGAPIpages(cd.users(), u'list', u'users', page_message=page_message,
                          message_attribute=u'primaryEmail', customer=GC_Values[GC_CUSTOMER_ID], query=u"orgUnitPath='%s'" % name,
                          fields=u'users(primaryEmail,orgUnitPath),nextPageToken', maxResults=GC_Values[GC_USER_MAX_RESULTS])
    for user in users:
      if show_children or (name.lower() == user[u'orgUnitPath'].lower()):
        sys.stdout.write(u' %s' % user[u'primaryEmail'])
        if name.lower() != user[u'orgUnitPath'].lower():
          print u' (child)'
        else:
          print u''

ORG_ARGUMENT_TO_PROPERTY_TITLE_MAP = {
  u'description': [u'description', u'Description'],
  u'id': [u'orgUnitId', u'ID'],
  u'inherit': [u'blockInheritance', u'InheritanceBlocked'],
  u'orgunitpath': [u'orgUnitPath', u'Path'],
  u'path': [u'orgUnitPath', u'Path'],
  u'name': [u'name', u'Name'],
  u'parent': [u'parentOrgUnitPath', u'Parent'],
  u'parentid': [u'parentOrgUnitId', u'ParentID'],
  }
ORG_FIELD_PRINT_ORDER = [u'orgunitpath', u'id', u'name', u'description', u'parent', u'parentid', u'inherit']

def doPrintOrgs():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  listType = u'all'
  orgUnitPath = u"/"
  todrive = False
  fieldsList = []
  fieldsTitles = {}
  titles = []
  csvRows = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'todrive':
      todrive = True
    elif myarg == u'toplevelonly':
      listType = u'children'
    elif myarg == u'fromparent':
      orgUnitPath = getOrgUnitPath()
    elif myarg == u'allfields':
      fieldsList = []
      fieldsTitles = {}
      titles = []
      for field in ORG_FIELD_PRINT_ORDER:
        addFieldTitleToCSVfile(field, ORG_ARGUMENT_TO_PROPERTY_TITLE_MAP, fieldsList, fieldsTitles, titles)
    elif myarg in ORG_ARGUMENT_TO_PROPERTY_TITLE_MAP:
      addFieldTitleToCSVfile(myarg, ORG_ARGUMENT_TO_PROPERTY_TITLE_MAP, fieldsList, fieldsTitles, titles)
    else:
      unknownArgumentExit()
  if not fieldsList:
    addFieldTitleToCSVfile(u'orgunitpath', ORG_ARGUMENT_TO_PROPERTY_TITLE_MAP, fieldsList, fieldsTitles, titles)
  sys.stderr.write(u"Retrieving All Organizational Units for your account (may take some time on large domain)...")
  orgs = callGAPI(cd.orgunits(), u'list',
                  customerId=GC_Values[GC_CUSTOMER_ID], type=listType, orgUnitPath=orgUnitPath, fields=u'organizationUnits({0})'.format(u','.join(set(fieldsList))))
  sys.stderr.write(u"done\n")
  if not u'organizationUnits' in orgs:
    print u'0 org units in this G Suite instance...'
    return
  for orgUnit in orgs[u'organizationUnits']:
    row = {}
    for field in fieldsList:
      row[fieldsTitles[field]] = orgUnit.get(field, u'')
    csvRows.append(row)
  writeCSVfile(csvRows, titles, u'Orgs', todrive)

ALIAS_TARGET_TYPES = [u'user', u'group', u'target',]

def doCreateAlias():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  body = {u'alias':  getEmailAddress(noUid=True)}
  target_type = getChoice(ALIAS_TARGET_TYPES)
  targetKey = getEmailAddress()
  checkForExtraneousArguments()
  print u'Creating alias %s for %s %s' % (body[u'alias'], target_type, targetKey)
  if target_type == u'user':
    callGAPI(cd.users().aliases(), u'insert', userKey=targetKey, body=body)
  elif target_type == u'group':
    callGAPI(cd.groups().aliases(), u'insert', groupKey=targetKey, body=body)
  elif target_type == u'target':
    try:
      callGAPI(cd.users().aliases(), u'insert', throw_reasons=[GAPI_INVALID, GAPI_BAD_REQUEST], userKey=targetKey, body=body)
    except (GAPI_invalid, GAPI_badRequest):
      callGAPI(cd.groups().aliases(), u'insert', groupKey=targetKey, body=body)

def doUpdateAlias():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  alias = getEmailAddress()
  target_type = getChoice(ALIAS_TARGET_TYPES)
  target_email = getEmailAddress()
  checkForExtraneousArguments()
  body = {u'alias': alias}
  try:
    callGAPI(cd.users().aliases(), u'delete', throw_reasons=[GAPI_INVALID], userKey=alias, alias=alias)
  except GAPI_invalid:
    callGAPI(cd.groups().aliases(), u'delete', groupKey=alias, alias=alias)
  if target_type == u'user':
    callGAPI(cd.users().aliases(), u'insert', userKey=target_email, body=body)
  elif target_type == u'group':
    callGAPI(cd.groups().aliases(), u'insert', groupKey=target_email, body=body)
  elif target_type == u'target':
    try:
      callGAPI(cd.users().aliases(), u'insert', throw_reasons=[GAPI_INVALID], userKey=target_email, body=body)
    except GAPI_invalid:
      callGAPI(cd.groups().aliases(), u'insert', groupKey=target_email, body=body)
  print u'updated alias %s' % alias

def doDeleteAlias(alias_email=None):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  if alias_email is None:
    targetType = getChoice(ALIAS_TARGET_TYPES, defaultChoice=u'target')
    alias_email = getString(OB_EMAIL_ADDRESS)
    checkForExtraneousArguments()
  else:
    targetType = u'target'
    alias_email = normalizeEmailAddressOrUID(alias_email)
  print u"Deleting alias %s" % alias_email
  if targetType != u'group':
    try:
      callGAPI(cd.users().aliases(), u'delete', throw_reasons=[GAPI_INVALID, GAPI_BAD_REQUEST, GAPI_NOT_FOUND], userKey=alias_email, alias=alias_email)
      return
    except (GAPI_invalid, GAPI_badRequest, GAPI_notFound) as e:
      error = json.loads(e.content)
      reason = error[u'error'][u'errors'][0][u'reason']
      if (reason == u'notFound') and (targetType == u'user'):
        systemErrorExit(4, u'The alias %s does not exist' % alias_email)
  callGAPI(cd.groups().aliases(), u'delete', groupKey=alias_email, alias=alias_email)

def doInfoAlias(alias_email=None):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  if alias_email is None:
    alias_email = getEmailAddress()
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
# Ignore info group/user arguments that may have come from whatis
    if (myarg in INFO_GROUP_OPTIONS) or (myarg in INFO_USER_OPTIONS):
      if myarg == u'schemas':
        getString(OB_SCHEMA_NAME_LIST)
    else:
      unknownArgumentExit()
  try:
    result = callGAPI(cd.users(), u'get', throw_reasons=[GAPI_INVALID, GAPI_BAD_REQUEST], userKey=alias_email)
  except (GAPI_invalid, GAPI_badRequest):
    result = callGAPI(cd.groups(), u'get', groupKey=alias_email)
  print u' Alias Email: %s' % alias_email
  try:
    if result[u'primaryEmail'].lower() == alias_email.lower():
      print u'Error: %s is a primary user email address, not an alias.' % alias_email
      sys.exit(3)
    print u' User Email: %s' % result[u'primaryEmail']
  except KeyError:
    print u' Group Email: %s' % result[u'email']
  print u' Unique ID: %s' % result[u'id']

def doPrintAliases():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  todrive = False
  titles = [u'Alias', u'Target', u'TargetType']
  csvRows = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  sys.stderr.write(u"Retrieving All User Aliases for %s organization (may take some time on large domain)...\n" % GC_Values[GC_DOMAIN])
  page_message = u'Got %%num_items%% users %%first_item%% - %%last_item%%\n'
  all_users = callGAPIpages(cd.users(), u'list', u'users', page_message=page_message,
                            message_attribute=u'primaryEmail', customer=GC_Values[GC_CUSTOMER_ID],
                            fields=u'users(primaryEmail,aliases),nextPageToken', maxResults=GC_Values[GC_USER_MAX_RESULTS])
  for user in all_users:
    try:
      for alias in user[u'aliases']:
        csvRows.append({u'Alias': alias, u'Target': user[u'primaryEmail'], u'TargetType': u'User'})
    except KeyError:
      continue
  sys.stderr.write(u"Retrieving All User Aliases for %s organization (may take some time on large domain)...\n" % GC_Values[GC_DOMAIN])
  page_message = u'Got %%num_items%% groups %%first_item%% - %%last_item%%\n'
  all_groups = callGAPIpages(cd.groups(), u'list', u'groups', page_message=page_message,
                             message_attribute=u'email', customer=GC_Values[GC_CUSTOMER_ID],
                             fields=u'groups(email,aliases),nextPageToken')
  for group in all_groups:
    try:
      for alias in group[u'aliases']:
        csvRows.append({u'Alias': alias, u'Target': group[u'email'], u'TargetType': u'Group'})
    except KeyError:
      continue
  writeCSVfile(csvRows, titles, u'Aliases', todrive)

def doUploadAuditKey():
  audit = getAuditObject()
  checkForExtraneousArguments()
  auditkey = sys.stdin.read()
  callGData(audit, u'updatePGPKey', pgpkey=auditkey)

def getAuditParameters(emailAddressRequired=True, requestIdRequired=True, destUserRequired=False):
  auditObject = getAuditObject()
  emailAddress = getEmailAddress(noUid=True, optional=not emailAddressRequired)
  parameters = {}
  if emailAddress:
    parameters[u'auditUser'] = emailAddress
    parameters[u'auditUserName'], auditObject.domain = splitEmailAddress(emailAddress)
    if requestIdRequired:
      parameters[u'requestId'] = getString(OB_REQUEST_ID)
    if destUserRequired:
      destEmailAddress = getEmailAddress(noUid=True)
      parameters[u'auditDestUser'] = destEmailAddress
      parameters[u'auditDestUserName'], destDomain = splitEmailAddress(destEmailAddress)
      if auditObject.domain != destDomain:
        putArgumentBack()
        invalidArgumentExit(u'{0}@{1}'.format(parameters[u'auditDestUserName'], auditObject.domain))
  return (auditObject, parameters)

def _showFileURLs(request):
  if u'numberOfFiles' in request:
    print u'  Number Of Files: '+request[u'numberOfFiles']
    for i in range(int(request[u'numberOfFiles'])):
      print u'   Url%s: %s' % (i, request[u'fileUrl%s' % i])

def _showMailboxActivityRequestStatus(request, showFiles=False):
  print u' Request ID: '+request[u'requestId']
  print u'  User: '+request[u'userEmailAddress']
  print u'  Status: '+request[u'status']
  print u'  Request Date: '+request[u'requestDate']
  print u'  Requested By: '+request[u'adminEmailAddress']
  if showFiles:
    _showFileURLs(request)

def doSubmitActivityRequest():
  audit, parameters = getAuditParameters(emailAddressRequired=True, requestIdRequired=False, destUserRequired=False)
  checkForExtraneousArguments()
  results = callGData(audit, u'createAccountInformationRequest',
                      user=parameters[u'auditUserName'])
  print u'Request successfully submitted:'
  _showMailboxActivityRequestStatus(results, showFiles=False)

def doDeleteActivityRequest():
  audit, parameters = getAuditParameters(emailAddressRequired=True, requestIdRequired=True, destUserRequired=False)
  checkForExtraneousArguments()
  callGData(audit, u'deleteAccountInformationRequest',
            user=parameters[u'auditUserName'], request_id=parameters[u'requestId'])

def doDownloadActivityRequest():
  audit, parameters = getAuditParameters(emailAddressRequired=True, requestIdRequired=True, destUserRequired=False)
  checkForExtraneousArguments()
  results = callGData(audit, u'getAccountInformationRequestStatus',
                      user=parameters[u'auditUserName'], request_id=parameters[u'requestId'])
  if results[u'status'] != u'COMPLETED':
    systemErrorExit(4, MESSAGE_REQUEST_NOT_COMPLETE.format(results[u'status']))
  if int(results.get(u'numberOfFiles', u'0')) < 1:
    systemErrorExit(4, MESSAGE_REQUEST_COMPLETED_NO_FILES)
  count = int(results[u'numberOfFiles'])
  for i in range(count):
    url = results[u'fileUrl'+str(i)]
    filename = u'activity-{0}-{1}-{2}.txt.jpg'.format(parameters[u'auditUserName'], parameters[u'requestId'], i)
    print u'Downloading {0}{1}'.format(filename, currentCount(i+1, count))
    geturl(url, filename)

def doStatusActivityRequests():
  audit, parameters = getAuditParameters(emailAddressRequired=False, requestIdRequired=True, destUserRequired=False)
  checkForExtraneousArguments()
  if parameters:
    results = callGData(audit, u'getAccountInformationRequestStatus',
                        user=parameters[u'auditUserName'], request_id=parameters[u'requestId'])
    print u''
    _showMailboxActivityRequestStatus(results, showFiles=True)
  else:
    results = callGData(audit, u'getAllAccountInformationRequestsStatus')
    print u'Current Activity Requests:'
    print u''
    for request in results:
      _showMailboxActivityRequestStatus(request, showFiles=True)
      print u''

def printMailboxExportRequestStatus(request, showFilter=False, showDates=False, showFiles=False):
  print u' Request ID: '+request[u'requestId']
  print u'  User: '+request[u'userEmailAddress']
  print u'  Status: '+request[u'status']
  print u'  Request Date: '+request[u'requestDate']
  print u'  Requested By: '+request[u'adminEmailAddress']
  print u'  Requested Parts: '+request[u'packageContent']
  if showFilter:
    print u'  Request Filter: '+request.get(u'searchQuery', u'None')
  print u'  Include Deleted: '+request[u'includeDeleted']
  if showDates:
    print u'  Begin: '+request.get(u'beginDate', u'Account creation date')
    print u'  End: '+request.get(u'endDate', u'Export request date')
  if showFiles:
    _showFileURLs(request)

def doSubmitRequestExport():
  audit, parameters = getAuditParameters(emailAddressRequired=True, requestIdRequired=False, destUserRequired=False)
  begin_date = end_date = search_query = None
  headers_only = include_deleted = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'begin':
      begin_date = getYYYYMMDD_HHMM()
    elif myarg == u'end':
      end_date = getYYYYMMDD_HHMM()
    elif myarg == u'search':
      search_query = getString(OB_QUERY)
    elif myarg == u'headersonly':
      headers_only = True
    elif myarg == u'includedeleted':
      include_deleted = True
    else:
      unknownArgumentExit()
  results = callGData(audit, u'createMailboxExportRequest',
                      user=parameters[u'auditUserName'], begin_date=begin_date, end_date=end_date, include_deleted=include_deleted,
                      search_query=search_query, headers_only=headers_only)
  print u'Export request successfully submitted:'
  printMailboxExportRequestStatus(results, showFilter=False, showDates=True, showFiles=False)

def doDeleteExportRequest():
  audit, parameters = getAuditParameters(emailAddressRequired=True, requestIdRequired=True, destUserRequired=False)
  checkForExtraneousArguments()
  callGData(audit, u'deleteMailboxExportRequest',
            user=parameters[u'auditUserName'], request_id=parameters[u'requestId'])

def doDownloadExportRequest():
  audit, parameters = getAuditParameters(emailAddressRequired=True, requestIdRequired=True, destUserRequired=False)
  checkForExtraneousArguments()
  results = callGData(audit, u'getMailboxExportRequestStatus',
                      user=parameters[u'auditUserName'], request_id=parameters[u'requestId'])
  if results[u'status'] != u'COMPLETED':
    systemErrorExit(4, MESSAGE_REQUEST_NOT_COMPLETE.format(results[u'status']))
  if int(results.get(u'numberOfFiles', u'0')) < 1:
    systemErrorExit(4, MESSAGE_REQUEST_COMPLETED_NO_FILES)
  count = int(results[u'numberOfFiles'])
  for i in range(count):
    url = results[u'fileUrl'+str(i)]
    filename = u'export-{0}-{1}-{2}.mbox.gpg'.format(parameters[u'auditUserName'], parameters[u'requestId'], i)
    #don't download existing files. This does not check validity of existing local
    #file so partial/corrupt downloads will need to be deleted manually.
    if not os.path.isfile(filename):
      print u'Downloading {0}{1}'.format(filename, currentCount(i+1, count))
      geturl(url, filename)

def doStatusExportRequests():
  audit, parameters = getAuditParameters(emailAddressRequired=False, requestIdRequired=True, destUserRequired=False)
  checkForExtraneousArguments()
  if parameters:
    results = callGData(audit, u'getMailboxExportRequestStatus',
                        user=parameters[u'auditUserName'], request_id=parameters[u'requestId'])
    print u''
    printMailboxExportRequestStatus(results, showFilter=True, showFiles=True)
  else:
    results = callGData(audit, u'getAllMailboxExportRequestsStatus')
    print u'Current Export Requests:'
    print u''
    for request in results:
      printMailboxExportRequestStatus(request, showFilter=True, showDates=False, showFiles=True)

def doWatchExportRequest():
  audit, parameters = getAuditParameters(emailAddressRequired=True, requestIdRequired=True, destUserRequired=False)
  checkForExtraneousArguments()
  while True:
    results = callGData(audit, u'getMailboxExportRequestStatus',
                        user=parameters[u'auditUserName'], request_id=parameters[u'requestId'])
    if results[u'status'] != u'PENDING':
      print u'status is %s. Sending email.' % results[u'status']
      msg_txt = u'\n'
      msg_txt += u'  Request ID: %s\n' % results[u'requestId']
      msg_txt += u'  User: %s\n' % results[u'userEmailAddress']
      msg_txt += u'  Status: %s\n' % results[u'status']
      msg_txt += u'  Request Date: %s\n' % results[u'requestDate']
      msg_txt += u'  Requested By: %s\n' % results[u'adminEmailAddress']
      msg_txt += u'  Requested Parts: %s\n' % results[u'packageContent']
      msg_txt += u'  Request Filter: %s\n' % results.get(u'searchQuery', u'None')
      msg_txt += u'  Include Deleted: %s\n' % results[u'includeDeleted']
      if u'numberOfFiles' in results:
        count = int(results[u'numberOfFiles'])
        msg_txt += u'  Number Of Files: {0}\n'.format(count)
        for i in range(count):
          msg_txt += u'  Url%s: %s\n' % (i, results[u'fileUrl%s' % i])
      msg_subj = u'Export #%s for %s status is %s' % (results[u'requestId'], results[u'userEmailAddress'], results[u'status'])
      send_email(msg_subj, msg_txt)
      break
    else:
      print u'status still PENDING, will check again in 5 minutes...'
      time.sleep(300)

def doCreateMonitor():
  audit, parameters = getAuditParameters(emailAddressRequired=True, requestIdRequired=False, destUserRequired=True)
  #end_date defaults to 30 days in the future...
  end_date = (datetime.datetime.now() + datetime.timedelta(days=30)).strftime(u"%Y-%m-%d %H:%M")
  begin_date = None
  incoming_headers_only = outgoing_headers_only = drafts_headers_only = chats_headers_only = False
  drafts = chats = True
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'end':
      end_date = getYYYYMMDD_HHMM()
    elif myarg == u'begin':
      begin_date = getYYYYMMDD_HHMM()
    elif myarg == u'incomingheaders':
      incoming_headers_only = True
    elif myarg == u'outgoingheaders':
      outgoing_headers_only = True
    elif myarg == u'nochats':
      chats = False
    elif myarg == u'nodrafts':
      drafts = False
    elif myarg == u'chatheaders':
      chats_headers_only = True
    elif myarg == u'draftheaders':
      drafts_headers_only = True
    else:
      unknownArgumentExit()
  callGData(audit, u'createEmailMonitor',
            source_user=parameters[u'auditUserName'], destination_user=parameters[u'auditDestUserName'], end_date=end_date, begin_date=begin_date,
            incoming_headers_only=incoming_headers_only, outgoing_headers_only=outgoing_headers_only,
            drafts=drafts, drafts_headers_only=drafts_headers_only, chats=chats, chats_headers_only=chats_headers_only)

def doDeleteMonitor():
  audit, parameters = getAuditParameters(emailAddressRequired=True, requestIdRequired=False, destUserRequired=True)
  checkForExtraneousArguments()
  callGData(audit, u'deleteEmailMonitor',
            source_user=parameters[u'auditUserName'], destination_user=parameters[u'auditDestUserName'])

def doShowMonitors():
  audit, parameters = getAuditParameters(emailAddressRequired=True, requestIdRequired=False, destUserRequired=False)
  checkForExtraneousArguments()
  results = callGData(audit, u'getEmailMonitors',
                      user=parameters[u'auditUserName'])
  print parameters[u'auditUser']+u' has the following monitors:'
  print u''
  for monitor in results:
    print u' Destination: '+monitor[u'destUserName']
    print u'  Begin: '+monitor.get(u'beginDate', u'immediately')
    print u'  End: '+monitor[u'endDate']
    print u'  Monitor Incoming: '+monitor[u'outgoingEmailMonitorLevel']
    print u'  Monitor Outgoing: '+monitor[u'incomingEmailMonitorLevel']
    print u'  Monitor Chats: '+monitor[u'chatMonitorLevel']
    print u'  Monitor Drafts: '+monitor[u'draftMonitorLevel']
    print u''

ACL_SCOPE_CHOICES = [u'default', u'user', u'group', u'domain',]

def getACLScope():
  scopeType = getChoice(ACL_SCOPE_CHOICES, defaultChoice=u'user')
  if scopeType == u'domain':
    entity = getString(OB_DOMAIN_NAME, optional=True)
    if entity:
      scopeValue = entity.lower()
    else:
      scopeValue = GC_Values[GC_DOMAIN]
  elif scopeType != u'default':
    scopeValue = getEmailAddress(noUid=True)
  else:
    scopeValue = None
  return (scopeType, scopeValue)

def getACLRuleId():
  scopeType, scopeValue = getACLScope()
  if scopeType != u'default':
    ruleId = u'{0}:{1}'.format(scopeType, scopeValue)
  else:
    ruleId = scopeType
  return ruleId

def formatACLRule(rule):
  if rule[u'scope'][u'type'] != u'default':
    return formatKeyValueList(u'(', [u'Scope', u'{0}:{1}'.format(rule[u'scope'][u'type'], rule[u'scope'][u'value']), u'Role', rule[u'role']], u')')
  else:
    return formatKeyValueList(u'(', [u'Scope', u'{0}'.format(rule[u'scope'][u'type']), u'Role', rule[u'role']], u')')

CALENDAR_ACL_ROLES_MAP = {
  u'editor': u'writer',
  u'freebusy': u'freeBusyReader',
  u'freebusyreader': u'freeBusyReader',
  u'owner': u'owner',
  u'read': u'reader',
  u'reader': u'reader',
  u'writer': u'writer',
  u'none': u'none',
  }

def doCalendarAddACL(cal, calendarId):
  role = getChoice(CALENDAR_ACL_ROLES_MAP, mapChoice=True)
  scopeType, scopeValue = getACLScope()
  checkForExtraneousArguments()
  body = {u'role': role, u'scope': {u'type': scopeType}}
  if scopeType != u'default':
    body[u'scope'][u'value'] = scopeValue
  callGAPI(cal.acl(), u'insert', calendarId=calendarId, body=body)

def doCalendarUpdateACL(cal, calendarId):
  body = {u'role': getChoice(CALENDAR_ACL_ROLES_MAP, mapChoice=True)}
  ruleId = getACLRuleId()
  checkForExtraneousArguments()
  callGAPI(cal.acl(), u'patch',
           calendarId=calendarId, ruleId=ruleId, body=body)

def doCalendarDeleteACL(cal, calendarId):
  getChoice(CALENDAR_ACL_ROLES_MAP, defaultChoice=None, mapChoice=True)
  ruleId = getACLRuleId()
  checkForExtraneousArguments()
  callGAPI(cal.acl(), u'delete',
           calendarId=calendarId, ruleId=ruleId)

def doCalendarShowACL(cal, calendarId):
  checkForExtraneousArguments()
  acls = callGAPIitems(cal.acl(), u'list', u'items', calendarId=calendarId)
  i = 0
  count = len(acls)
  for rule in acls:
    i += 1
    print u'Calendar: {0}, ACL: {1}{2}'.format(calendarId, formatACLRule(rule), currentCount(i, count))

CALENDAR_EVENT_VISIBILITY_CHOICES = [u'default', u'public', u'private',]

def doCalendarAddEvent(cal, calendarId):
  calendarId, cal = buildCalendarGAPIObject(calendarId)
  if not cal:
    return
  sendNotifications = timeZone = None
  body = {}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'notifyattendees':
      sendNotifications = True
    elif myarg == u'attendee':
      body.setdefault(u'attendees', [])
      body[u'attendees'].append({u'email': getEmailAddress(noUid=True)})
    elif myarg == u'optionalattendee':
      body.setdefault(u'attendees', [])
      body[u'attendees'].append({u'email': getEmailAddress(noUid=True), u'optional': True})
    elif myarg == u'anyonecanaddself':
      body[u'anyoneCanAddSelf'] = True
    elif myarg == u'description':
      body[u'description'] = getString(OB_STRING)
    elif myarg == u'start':
      body[u'start'] = getEventTime()
    elif myarg == u'end':
      body[u'end'] = getEventTime()
    elif myarg == u'guestscantinviteothers':
      body[u'guestsCanInviteOthers'] = False
    elif myarg == u'guestscantseeothers':
      body[u'guestsCanSeeOtherGuests'] = False
    elif myarg == u'id':
      body[u'id'] = getString(OB_STRING)
    elif myarg == u'summary':
      body[u'summary'] = getString(OB_STRING)
    elif myarg == u'location':
      body[u'location'] = getString(OB_STRING)
    elif myarg == u'available':
      body[u'transparency'] = u'transparent'
    elif myarg == u'visibility':
      body[u'visibility'] = getChoice(CALENDAR_EVENT_VISIBILITY_CHOICES)
    elif myarg == u'tentative':
      body[u'status'] = u'tentative'
    elif myarg == u'source':
      body[u'source'] = {u'title': getString(OB_STRING), u'url': getString(OB_STRING)}
    elif myarg == u'noreminders':
      body[u'reminders'] = {u'useDefault': False}
    elif myarg == u'reminder':
      body.setdefault(u'reminders', {u'overrides': [], u'useDefault': False})
      body[u'reminders'][u'overrides'].append(getCalendarReminder())
      body[u'reminders'][u'useDefault'] = False
    elif myarg == u'recurrence':
      body.setdefault(u'recurrence', [])
      body[u'recurrence'].append(getString(OB_RECURRENCE))
    elif myarg == u'timezone':
      timeZone = getString(OB_STRING)
    elif myarg == u'privateproperty':
      body.setdefault(u'extendedProperties', {u'private': {}, u'shared': {}})
      key = getString(OB_PROPERTY_KEY)
      body[u'extendedProperties'][u'private'][key] = getString(OB_PROPERTY_VALUE)
    elif myarg == u'sharedproperty':
      body.setdefault(u'extendedProperties', {u'private': {}, u'shared': {}})
      key = getString(OB_PROPERTY_KEY)
      body[u'extendedProperties'][u'shared'][key] = getString(OB_PROPERTY_VALUE)
    elif myarg == u'colorindex':
      body[u'colorId'] = str(getInteger(CALENDAR_EVENT_MIN_COLOR_INDEX, CALENDAR_EVENT_MAX_COLOR_INDEX))
    else:
      unknownArgumentExit()
  if not timeZone and u'recurrence' in body:
    timeZone = callGAPI(cal.calendars(), u'get', calendarId=calendarId, fields=u'timeZone')[u'timeZone']
  if u'recurrence' in body:
    for a_time in [u'start', u'end']:
      try:
        body[a_time][u'timeZone'] = timeZone
      except KeyError:
        pass
  callGAPI(cal.events(), u'insert', calendarId=calendarId, sendNotifications=sendNotifications, body=body)

def doCalendarDeleteEvent(cal, calendarId):
  calendarId, cal = buildCalendarGAPIObject(calendarId)
  if not cal:
    return
  events = []
  sendNotifications = None
  doIt = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'notifyattendees':
      sendNotifications = True
    elif myarg in [u'id', u'eventid']:
      events.append(getString(OB_EVENT_ID))
    elif myarg in [u'q', u'query', u'eventquery']:
      query = getString(OB_QUERY)
      result = callGAPIpages(cal.events(), u'list', items=u'items', calendarId=calendarId, q=query)
      for event in result:
        if u'id' in event and event[u'id'] not in events:
          events.append(event[u'id'])
    elif myarg == u'doit':
      doIt = True
    else:
      unknownArgumentExit()
  if doIt:
    for eventId in events:
      print u' deleting eventId %s' % eventId
      callGAPI(cal.events(), u'delete', calendarId=calendarId, eventId=eventId, sendNotifications=sendNotifications)
  else:
    for eventId in events:
      print u' would delete eventId %s. Add doit to command to actually delete event' % eventId

def doCalendarWipeEvents(cal, calendarId):
  checkForExtraneousArguments()
  calendarId, cal = buildCalendarGAPIObject(calendarId)
  if not cal:
    return
  callGAPI(cal.calendars(), u'clear', calendarId=calendarId)

# Utilities for cros commands
def getCrOSDeviceEntity():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  if checkArgumentPresent(QUERY_ARGUMENT):
    query = getString(OB_QUERY)
  else:
    deviceId = getString(OB_CROS_DEVICE_ENTITY)
    if deviceId[:6].lower() == u'query:':
      query = deviceId[6:]
    else:
      query = None
  if not query:
    return (deviceId.replace(u',', u' ').split(), cd)
  devices = callGAPIpages(cd.chromeosdevices(), u'list', u'chromeosdevices',
                          customerId=GC_Values[GC_CUSTOMER_ID], query=query,
                          fields=u'nextPageToken,chromeosdevices(deviceId)')
  return ([cros[u'deviceId'] for cros in devices], cd)

UPDATE_CROS_ARGUMENT_TO_PROPERTY_MAP = {
  u'annotatedassetid': u'annotatedAssetId',
  u'annotatedlocation': u'annotatedLocation',
  u'annotateduser': u'annotatedUser',
  u'asset': u'annotatedAssetId',
  u'assetid': u'annotatedAssetId',
  u'location': u'annotatedLocation',
  u'notes': u'notes',
  u'org': u'orgUnitPath',
  u'orgunitpath': u'orgUnitPath',
  u'ou': u'orgUnitPath',
  u'tag': u'annotatedAssetId',
  u'user': u'annotatedUser',
  }

CROS_ACTION_CHOICES_MAP = {
  u'deprovisionsamemodelreplace': (u'deprovision', u'same_model_replacement'),
  u'deprovisionsamemodelreplacement': (u'deprovision', u'same_model_replacement'),
  u'deprovisiondifferentmodelreplace': (u'deprovision', u'different_model_replacement'),
  u'deprovisiondifferentmodelreplacement': (u'deprovision', u'different_model_replacement'),
  u'deprovisionretiringdevice': (u'deprovision', u'retiring_device'),
  u'disable': (u'disable', None),
  u'reenable': (u'reenable', None)
  }

def doUpdateCrosDevice():
  devices, cd = getCrOSDeviceEntity()
  update_body = {}
  action_body = {}
  ack_wipe = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg in UPDATE_CROS_ARGUMENT_TO_PROPERTY_MAP:
      up = UPDATE_CROS_ARGUMENT_TO_PROPERTY_MAP[myarg]
      if up == u'orgUnitPath':
        update_body[up] = getOrgUnitPath()
      elif up == u'notes':
        update_body[up] = getString(OB_STRING, minLen=0).replace(u'\\n', u'\n')
      else:
        update_body[up] = getString(OB_STRING, minLen=[0, 1][up == u'annotatedAssetId'])
    elif myarg == u'action':
      action_body[u'action'], deprovisionReason = getChoice(CROS_ACTION_CHOICES_MAP, mapChoice=True)
      if deprovisionReason:
        action_body[u'deprovisionReason'] = deprovisionReason
    elif myarg == u'acknowledgedevicetouchrequirement':
      ack_wipe = True
    else:
      unknownArgumentExit()
  i = 0
  count = len(devices)
  if action_body:
    if action_body[u'action'] == u'deprovision' and not ack_wipe:
      stderrWarningMsg(MESSAGE_REFUSING_TO_DEPROVISION_DEVICES.format(count))
      sys.exit(AC_NOT_PERFORMED_RC)
    for deviceId in devices:
      i += 1
      print u'Action CrOS Device: {0}, {1}{2}'.format(deviceId, action_body[u'action'], currentCount(i, count))
      callGAPI(cd.chromeosdevices(), function=u'action', customerId=GC_Values[GC_CUSTOMER_ID], resourceId=deviceId, body=action_body)
  elif update_body:
    for deviceId in devices:
      i += 1
      print u'Update CrOS Device: {0}{1}'.format(deviceId, currentCount(i, count))
      callGAPI(cd.chromeosdevices(), u'patch', customerId=GC_Values[GC_CUSTOMER_ID], deviceId=deviceId, body=update_body)

CROS_ARGUMENT_TO_PROPERTY_MAP = {
  u'activetimeranges': [u'activeTimeRanges.activeTime', u'activeTimeRanges.date'],
  u'annotatedassetid': [u'annotatedAssetId',],
  u'annotatedlocation': [u'annotatedLocation',],
  u'annotateduser': [u'annotatedUser',],
  u'asset': [u'annotatedAssetId',],
  u'assetid': [u'annotatedAssetId',],
  u'bootmode': [u'bootMode',],
  u'deviceid': [u'deviceId',],
  u'ethernetmacaddress': [u'ethernetMacAddress',],
  u'firmwareversion': [u'firmwareVersion',],
  u'lastenrollmenttime': [u'lastEnrollmentTime',],
  u'lastsync': [u'lastSync',],
  u'location': [u'annotatedLocation',],
  u'macaddress': [u'macAddress',],
  u'meid': [u'meid',],
  u'model': [u'model',],
  u'notes': [u'notes',],
  u'ordernumber': [u'orderNumber',],
  u'org': [u'orgUnitPath',],
  u'orgunitpath': [u'orgUnitPath',],
  u'osversion': [u'osVersion',],
  u'ou': [u'orgUnitPath',],
  u'platformversion': [u'platformVersion',],
  u'recentusers': [u'recentUsers.email', u'recentUsers.type'],
  u'serialnumber': [u'serialNumber',],
  u'status': [u'status',],
  u'supportenddate': [u'supportEndDate',],
  u'tag': [u'annotatedAssetId',],
  u'timeranges': [u'activeTimeRanges.activeTime', u'activeTimeRanges.date'],
  u'user': [u'annotatedUser',],
  u'willautorenew': [u'willAutoRenew',],
  }

CROS_BASIC_FIELDS_LIST = [u'deviceId', u'annotatedAssetId', u'annotatedLocation', u'annotatedUser', u'lastSync', u'notes', u'serialNumber', u'status']

CROS_SCALAR_PROPERTY_PRINT_ORDER = [
  u'orgUnitPath',
  u'annotatedAssetId',
  u'annotatedLocation',
  u'annotatedUser',
  u'lastSync',
  u'notes',
  u'serialNumber',
  u'status',
  u'model',
  u'firmwareVersion',
  u'platformVersion',
  u'osVersion',
  u'bootMode',
  u'meid',
  u'ethernetMacAddress',
  u'macAddress',
  u'lastEnrollmentTime',
  u'orderNumber',
  u'supportEndDate',
  u'willAutoRenew',
  ]

def doInfoCrosDevice():
  devices, cd = getCrOSDeviceEntity()
  projection = None
  fieldsList = []
  noLists = False
  listLimit = 0
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'nolists':
      noLists = True
    elif myarg == u'listlimit':
      listLimit = getInteger(minVal=0)
    elif myarg == u'allfields':
      projection = u'FULL'
      fieldsList = []
    elif myarg in PROJECTION_CHOICES_MAP:
      projection = PROJECTION_CHOICES_MAP[myarg]
      if projection == u'FULL':
        fieldsList = []
      else:
        fieldsList = CROS_BASIC_FIELDS_LIST[:]
    elif myarg in CROS_ARGUMENT_TO_PROPERTY_MAP:
      if not fieldsList:
        fieldsList = [u'deviceId',]
      fieldsList.extend(CROS_ARGUMENT_TO_PROPERTY_MAP[myarg])
    elif myarg == u'fields':
      if not fieldsList:
        fieldsList = [u'deviceId',]
      fieldNameList = getString(OB_FIELD_NAME_LIST)
      for field in fieldNameList.lower().replace(u',', u' ').split():
        if field in CROS_ARGUMENT_TO_PROPERTY_MAP:
          fieldsList.extend(CROS_ARGUMENT_TO_PROPERTY_MAP[field])
          if field in [u'recentusers', u'timeranges', u'activetimeranges']:
            projection = u'FULL'
            noLists = False
        else:
          putArgumentBack()
          invalidChoiceExit(CROS_ARGUMENT_TO_PROPERTY_MAP)
    else:
      unknownArgumentExit()
  if fieldsList:
    fields = u','.join(set(fieldsList)).replace(u'.', u'/')
  else:
    fields = None
  i = 0
  count = len(devices)
  for deviceId in devices:
    i += 1
    cros = callGAPI(cd.chromeosdevices(), u'get', customerId=GC_Values[GC_CUSTOMER_ID],
                    deviceId=deviceId, projection=projection, fields=fields)
    print u'CrOS Device: {0}{1}'.format(deviceId, currentCount(i, count))
    if u'notes' in cros:
      cros[u'notes'] = cros[u'notes'].replace(u'\n', u'\\n')
    for up in CROS_SCALAR_PROPERTY_PRINT_ORDER:
      if up in cros:
        print u'  {0}: {1}'.format(up, cros[up])
    if not noLists:
      activeTimeRanges = cros.get(u'activeTimeRanges', [])
      lenATR = len(activeTimeRanges)
      if lenATR:
        print u'  activeTimeRanges'
        for j in xrange(min(listLimit, lenATR) if listLimit else lenATR):
          print u'    date: {0}'.format(activeTimeRanges[j][u'date'])
          print u'      activeTime: {0}'.format(str(activeTimeRanges[j][u'activeTime']))
          print u'      duration: {0}'.format(formatMilliSeconds(activeTimeRanges[j][u'activeTime']))
      recentUsers = cros.get(u'recentUsers', [])
      lenRU = len(recentUsers)
      if lenRU:
        print u'  recentUsers'
        for j in xrange(min(listLimit, lenRU) if listLimit else lenRU):
          print u'    type: {0}'.format(recentUsers[j][u'type'])
          print u'      email: {0}'.format(recentUsers[j].get(u'email', u''))

CROS_ORDERBY_CHOICES_MAP = {
  u'lastsync': u'lastSync',
  u'location': u'annotatedLocation',
  u'notes': u'notes',
  u'serialnumber': u'serialNumber',
  u'status': u'status',
  u'supportenddate': u'supportEndDate',
  u'user': u'annotatedUser',
  }

def doPrintCrosDevices():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  todrive = False
  fieldsList = []
  fieldsTitles = {}
  titles = []
  csvRows = []
  addFieldToCSVfile(u'deviceid', CROS_ARGUMENT_TO_PROPERTY_MAP, fieldsList, fieldsTitles, titles)
  sortHeaders = False
  query = projection = orderBy = sortOrder = None
  noLists = False
  listLimit = 0
  selectActiveTimeRanges = selectRecentUsers = None
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'query':
      query = getString(OB_QUERY)
    elif myarg == u'todrive':
      todrive = True
    elif myarg == u'nolists':
      noLists = True
      selectActiveTimeRanges = selectRecentUsers = None
    elif myarg == u'recentusers':
      projection = u'FULL'
      selectRecentUsers = u'recentUsers'
      noLists = False
      if fieldsList:
        fieldsList.append(selectRecentUsers)
    elif myarg in [u'timeranges', u'activetimeranges']:
      projection = u'FULL'
      selectActiveTimeRanges = u'activeTimeRanges'
      noLists = False
      if fieldsList:
        fieldsList.append(selectActiveTimeRanges)
    elif myarg == u'listlimit':
      listLimit = getInteger(minVal=1)
    elif myarg == u'orderby':
      orderBy = getChoice(CROS_ORDERBY_CHOICES_MAP, mapChoice=True)
    elif myarg in SORTORDER_CHOICES_MAP:
      sortOrder = SORTORDER_CHOICES_MAP[myarg]
    elif myarg in PROJECTION_CHOICES_MAP:
      projection = PROJECTION_CHOICES_MAP[myarg]
      sortHeaders = True
      if projection == u'FULL':
        fieldsList = []
      else:
        fieldsList = CROS_BASIC_FIELDS_LIST[:]
    elif myarg == u'allfields':
      projection = u'FULL'
      sortHeaders = True
      fieldsList = []
    elif myarg in CROS_ARGUMENT_TO_PROPERTY_MAP:
      if not fieldsList:
        fieldsList = [u'deviceId',]
      addFieldToCSVfile(myarg, CROS_ARGUMENT_TO_PROPERTY_MAP, fieldsList, fieldsTitles, titles)
    elif myarg == u'fields':
      if not fieldsList:
        fieldsList = [u'deviceId',]
      fieldNameList = getString(OB_FIELD_NAME_LIST)
      for field in fieldNameList.lower().replace(u',', u' ').split():
        if field in CROS_ARGUMENT_TO_PROPERTY_MAP:
          addFieldToCSVfile(field, CROS_ARGUMENT_TO_PROPERTY_MAP, fieldsList, fieldsTitles, titles)
          if field == u'recentusers':
            projection = u'FULL'
            selectRecentUsers = u'recentUsers'
            noLists = False
          elif field in [u'timeranges', u'activetimeranges']:
            projection = u'FULL'
            selectActiveTimeRanges = u'activeTimeRanges'
            noLists = False
        else:
          putArgumentBack()
          invalidChoiceExit(CROS_ARGUMENT_TO_PROPERTY_MAP)
    else:
      unknownArgumentExit()
  if fieldsList:
    fields = u'nextPageToken,chromeosdevices({0})'.format(u','.join(set(fieldsList))).replace(u'.', u'/')
  else:
    fields = None
  sys.stderr.write(u'Retrieving All Chrome OS Devices for organization (may take some time for large accounts)...\n')
  page_message = u'Got %%num_items%% Chrome devices...\n'
  feed = callGAPIpages(cd.chromeosdevices(), u'list', u'chromeosdevices', page_message=page_message,
                       query=query, customerId=GC_Values[GC_CUSTOMER_ID], projection=projection,
                       orderBy=orderBy, sortOrder=sortOrder, fields=fields, maxResults=GC_Values[GC_DEVICE_MAX_RESULTS])
  if feed:
    if (not noLists) and (not selectActiveTimeRanges) and (not selectRecentUsers):
      while feed:
        cros = feed.popleft()
        if u'notes' in cros:
          cros[u'notes'] = cros[u'notes'].replace(u'\n', u'\\n')
        addRowTitlesToCSVfile(flattenJSON(cros, listLimit=listLimit), csvRows, titles)
    else:
      if not noLists:
        if selectActiveTimeRanges:
          for attrib in [u'activeTimeRanges.activeTime', u'activeTimeRanges.date']:
            titles.append(attrib)
        if selectRecentUsers:
          for attrib in [u'recentUsers.email', u'recentUsers.type']:
            titles.append(attrib)
      while feed:
        cros = feed.popleft()
        if u'notes' in cros:
          cros[u'notes'] = cros[u'notes'].replace(u'\n', u'\\n')
        row = {}
        for attrib in cros:
          if attrib in [u'kind', u'etag', u'recentUsers', u'activeTimeRanges']:
            continue
          if attrib not in titles:
            titles.append(attrib)
          row[attrib] = cros[attrib]
        activeTimeRanges = cros.get(selectActiveTimeRanges, []) if selectActiveTimeRanges else []
        recentUsers = cros.get(selectRecentUsers, []) if selectRecentUsers else []
        if noLists or (not activeTimeRanges and not recentUsers):
          csvRows.append(row)
        else:
          lenATR = len(activeTimeRanges)
          lenRU = len(recentUsers)
          for i in xrange(min(listLimit, max(lenATR, lenRU)) if listLimit else max(lenATR, lenRU)):
            new_row = row.copy()
            if i < lenATR:
              new_row[u'activeTimeRanges.activeTime'] = str(activeTimeRanges[i][u'activeTime'])
              new_row[u'activeTimeRanges.date'] = activeTimeRanges[i][u'date']
            if i < lenRU:
              new_row[u'recentUsers.email'] = recentUsers[i].get(u'email', u'')
              new_row[u'recentUsers.type'] = recentUsers[i][u'type']
            csvRows.append(new_row)
  if sortHeaders:
    sortCSVTitles([u'deviceId',], titles)
  writeCSVfile(csvRows, titles, u'CrOS', todrive)

MOBILE_ACTION_CHOICE_MAP = {
  u'accountwipe': u'admin_account_wipe',
  u'adminaccountwipe': u'admin_account_wipe',
  u'wipeaccount': u'admin_account_wipe',
  u'adminremotewipe': u'admin_remote_wipe',
  u'wipe': u'admin_remote_wipe',
  u'approve': u'approve',
  u'block': u'action_block',
  u'cancelremotewipethenactivate': u'cancel_remote_wipe_then_activate',
  u'cancelremotewipethenblock': u'cancel_remote_wipe_then_block',
  }

def doUpdateMobileDevice():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  resourceId = getString(OB_MOBILE_DEVICE_ENTITY)
  action_body = {}
  patch_body = {}
  doPatch = doAction = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'action':
      action_body[u'action'] = getChoice(MOBILE_ACTION_CHOICE_MAP, mapChoice=True)
      doAction = True
    elif myarg == u'model':
      patch_body[u'model'] = getString(OB_STRING)
      doPatch = True
    elif myarg == u'os':
      patch_body[u'os'] = getString(OB_STRING)
      doPatch = True
    elif myarg == u'useragent':
      patch_body[u'userAgent'] = getString(OB_STRING)
      doPatch = True
    else:
      unknownArgumentExit()
  if doPatch:
    callGAPI(cd.mobiledevices(), u'patch', resourceId=resourceId, body=patch_body, customerId=GC_Values[GC_CUSTOMER_ID])
  if doAction:
    callGAPI(cd.mobiledevices(), u'action', resourceId=resourceId, body=action_body, customerId=GC_Values[GC_CUSTOMER_ID])

def doDeleteMobileDevice():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  resourceId = getString(OB_MOBILE_DEVICE_ENTITY)
  checkForExtraneousArguments()
  callGAPI(cd.mobiledevices(), u'delete', resourceId=resourceId, customerId=GC_Values[GC_CUSTOMER_ID])

def doInfoMobileDevice():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  deviceId = getString(OB_MOBILE_DEVICE_ENTITY)
  checkForExtraneousArguments()
  info = callGAPI(cd.mobiledevices(), u'get', customerId=GC_Values[GC_CUSTOMER_ID], resourceId=deviceId)
  showJSON(None, info)

MOBILE_ORDERBY_CHOICES_MAP = {
  u'deviceid': u'deviceId',
  u'email': u'email',
  u'lastsync': u'lastSync',
  u'model': u'model',
  u'name': u'name',
  u'os': u'os',
  u'status': u'status',
  u'type': u'type',
  }

MOBILE_PROJECTION_BASIC = u'BASIC'
MOBILE_PROJECTION_FULL = u'FULL'

MOBILE_PROJECTION_CHOICES_MAP = {
  u'basic': MOBILE_PROJECTION_BASIC,
  u'full': MOBILE_PROJECTION_FULL,
  }

def doPrintMobileDevices():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  todrive = False
  titles = [u'resourceId',]
  csvRows = []
  query = projection = orderBy = sortOrder = None
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'query':
      query = getString(OB_QUERY)
    elif myarg == u'todrive':
      todrive = True
    elif myarg == u'orderby':
      orderBy = getChoice(MOBILE_ORDERBY_CHOICES_MAP, mapChoice=True)
    elif myarg in SORTORDER_CHOICES_MAP:
      sortOrder = SORTORDER_CHOICES_MAP[myarg]
    elif myarg in MOBILE_PROJECTION_CHOICES_MAP:
      projection = MOBILE_PROJECTION_CHOICES_MAP[myarg]
    else:
      unknownArgumentExit()
  sys.stderr.write(u'Retrieving All Mobile Devices for organization (may take some time for large accounts)...\n')
  page_message = u'Got %%num_items%% mobile devices...\n'
  feed = callGAPIpages(cd.mobiledevices(), u'list', u'mobiledevices', page_message=page_message,
                       customerId=GC_Values[GC_CUSTOMER_ID], query=query, projection=projection,
                       orderBy=orderBy, sortOrder=sortOrder, maxResults=GC_Values[GC_DEVICE_MAX_RESULTS])
  while feed:
    mobile = feed.popleft()
    row = {}
    for attrib in mobile:
      if attrib in [u'kind', u'etag', u'applications']:
        continue
      if attrib not in titles:
        titles.append(attrib)
      if attrib in [u'name', u'email']:
        if mobile[attrib]:
          row[attrib] = mobile[attrib][0]
      else:
        row[attrib] = mobile[attrib]
    csvRows.append(row)
  writeCSVfile(csvRows, titles, u'Mobile', todrive)

GROUP_ATTRIBUTES = {
  u'allowexternalmembers': [u'allowExternalMembers', {GC_VAR_TYPE: GC_TYPE_BOOLEAN}],
  u'allowgooglecommunication': [u'allowGoogleCommunication', {GC_VAR_TYPE: GC_TYPE_BOOLEAN}],
  u'allowwebposting': [u'allowWebPosting', {GC_VAR_TYPE: GC_TYPE_BOOLEAN}],
  u'archiveonly': [u'archiveOnly', {GC_VAR_TYPE: GC_TYPE_BOOLEAN}],
  u'customfootertext': [u'customFooterText', {GC_VAR_TYPE: GC_TYPE_STRING}],
  u'customreplyto': [u'customReplyTo', {GC_VAR_TYPE: GC_TYPE_EMAIL}],
  u'defaultmessagedenynotificationtext': [u'defaultMessageDenyNotificationText', {GC_VAR_TYPE: GC_TYPE_STRING}],
  u'description': [u'description', {GC_VAR_TYPE: GC_TYPE_STRING}],
  u'gal': [u'includeInGlobalAddressList', {GC_VAR_TYPE: GC_TYPE_BOOLEAN}],
  u'includecustomfooter': [u'includeCustomFooter', {GC_VAR_TYPE: GC_TYPE_BOOLEAN}],
  u'includeinglobaladdresslist': [u'includeInGlobalAddressList', {GC_VAR_TYPE: GC_TYPE_BOOLEAN}],
  u'isarchived': [u'isArchived', {GC_VAR_TYPE: GC_TYPE_BOOLEAN}],
  u'maxmessagebytes': [u'maxMessageBytes', {GC_VAR_TYPE: GC_TYPE_INTEGER}],
  u'memberscanpostasthegroup': [u'membersCanPostAsTheGroup', {GC_VAR_TYPE: GC_TYPE_BOOLEAN}],
  u'messagedisplayfont': [u'messageDisplayFont', {GC_VAR_TYPE: GC_TYPE_CHOICE,
                                                  u'choices': {u'defaultfont': u'DEFAULT_FONT', u'fixedwidthfont': u'FIXED_WIDTH_FONT',}}],
  u'messagemoderationlevel': [u'messageModerationLevel', {GC_VAR_TYPE: GC_TYPE_CHOICE,
                                                          u'choices': {u'moderateallmessages': u'MODERATE_ALL_MESSAGES', u'moderatenonmembers': u'MODERATE_NON_MEMBERS',
                                                                       u'moderatenewmembers': u'MODERATE_NEW_MEMBERS', u'moderatenone': u'MODERATE_NONE',}}],
  u'name': [u'name', {GC_VAR_TYPE: GC_TYPE_STRING}],
  u'primarylanguage': [u'primaryLanguage', {GC_VAR_TYPE: GC_TYPE_LANGUAGE}],
  u'replyto': [u'replyTo', {GC_VAR_TYPE: GC_TYPE_CHOICE,
                            u'choices': {u'replytocustom': u'REPLY_TO_CUSTOM', u'replytosender': u'REPLY_TO_SENDER', u'replytolist': u'REPLY_TO_LIST',
                                         u'replytoowner': u'REPLY_TO_OWNER', u'replytoignore': u'REPLY_TO_IGNORE', u'replytomanagers': u'REPLY_TO_MANAGERS',}}],
  u'sendmessagedenynotification': [u'sendMessageDenyNotification', {GC_VAR_TYPE: GC_TYPE_BOOLEAN}],
  u'showingroupdirectory': [u'showInGroupDirectory', {GC_VAR_TYPE: GC_TYPE_BOOLEAN}],
  u'spammoderationlevel': [u'spamModerationLevel', {GC_VAR_TYPE: GC_TYPE_CHOICE,
                                                    u'choices': {u'allow': u'ALLOW', u'moderate': u'MODERATE', u'silentlymoderate': u'SILENTLY_MODERATE', u'reject': u'REJECT',}}],
  u'whocanadd': [u'whoCanAdd', {GC_VAR_TYPE: GC_TYPE_CHOICE,
                                u'choices': {u'allmemberscanadd': u'ALL_MEMBERS_CAN_ADD', u'allmanagerscanadd': u'ALL_MANAGERS_CAN_ADD', u'nonecanadd': u'NONE_CAN_ADD',}}],
  u'whocancontactowner': [u'whoCanContactOwner', {GC_VAR_TYPE: GC_TYPE_CHOICE,
                                                  u'choices': {u'anyonecancontact': u'ANYONE_CAN_CONTACT', u'allindomaincancontact': u'ALL_IN_DOMAIN_CAN_CONTACT',
                                                               u'allmemberscancontact': u'ALL_MEMBERS_CAN_CONTACT', u'allmanagerscancontact': u'ALL_MANAGERS_CAN_CONTACT',}}],
  u'whocaninvite': [u'whoCanInvite', {GC_VAR_TYPE: GC_TYPE_CHOICE,
                                      u'choices': {u'allmemberscaninvite': u'ALL_MEMBERS_CAN_INVITE', u'allmanagerscaninvite': u'ALL_MANAGERS_CAN_INVITE', u'nonecaninvite': u'NONE_CAN_INVITE',}}],
  u'whocanjoin': [u'whoCanJoin', {GC_VAR_TYPE: GC_TYPE_CHOICE,
                                  u'choices': {u'anyonecanjoin': u'ANYONE_CAN_JOIN', u'allindomaincanjoin': u'ALL_IN_DOMAIN_CAN_JOIN',
                                               u'invitedcanjoin': u'INVITED_CAN_JOIN', u'canrequesttojoin': u'CAN_REQUEST_TO_JOIN',}}],
  u'whocanleavegroup': [u'whoCanLeaveGroup', {GC_VAR_TYPE: GC_TYPE_CHOICE,
                                              u'choices': {u'allmanagerscanleave': u'ALL_MANAGERS_CAN_LEAVE', u'allmemberscanleave': u'ALL_MEMBERS_CAN_LEAVE', u'nonecanleave': u'NONE_CAN_LEAVE',}}],
  u'whocanpostmessage': [u'whoCanPostMessage', {GC_VAR_TYPE: GC_TYPE_CHOICE,
                                                u'choices': {u'nonecanpost': u'NONE_CAN_POST', u'allmanagerscanpost': u'ALL_MANAGERS_CAN_POST', u'allmemberscanpost': u'ALL_MEMBERS_CAN_POST',
                                                             u'allindomaincanpost': u'ALL_IN_DOMAIN_CAN_POST', u'anyonecanpost': u'ANYONE_CAN_POST',}}],
  u'whocanviewgroup': [u'whoCanViewGroup', {GC_VAR_TYPE: GC_TYPE_CHOICE,
                                            u'choices': {u'anyonecanview': u'ANYONE_CAN_VIEW', u'allindomaincanview': u'ALL_IN_DOMAIN_CAN_VIEW',
                                                         u'allmemberscanview': u'ALL_MEMBERS_CAN_VIEW', u'allmanagerscanview': u'ALL_MANAGERS_CAN_VIEW',}}],
  u'whocanviewmembership': [u'whoCanViewMembership', {GC_VAR_TYPE: GC_TYPE_CHOICE,
                                                      u'choices': {u'allindomaincanview': u'ALL_IN_DOMAIN_CAN_VIEW', u'allmemberscanview': u'ALL_MEMBERS_CAN_VIEW',
                                                                   u'allmanagerscanview': u'ALL_MANAGERS_CAN_VIEW',}}],
  }

GROUP_FIELDS_WITH_CRS_NLS = [u'customFooterText', u'defaultMessageDenyNotificationText', u'description']

def getGroupAttrValue(argument, gs_body):
  attrProperties = GROUP_ATTRIBUTES.get(argument)
  if not attrProperties:
    unknownArgumentExit()
  attrName = attrProperties[0]
  attribute = attrProperties[1]
  attrType = attribute[GC_VAR_TYPE]
  if attrType == GC_TYPE_BOOLEAN:
    gs_body[attrName] = getBoolean()
  elif attrType == GC_TYPE_STRING:
    if attrName in GROUP_FIELDS_WITH_CRS_NLS:
      gs_body[attrName] = getString(OB_STRING, minLen=0).replace(u'\\n', u'\n')
    else:
      gs_body[attrName] = getString(OB_STRING, minLen=0)
  elif attrType == GC_TYPE_CHOICE:
    gs_body[attrName] = getChoice(attribute[u'choices'], mapChoice=True)
  elif attrType == GC_TYPE_EMAIL:
    gs_body[attrName] = getEmailAddress(noUid=True)
  elif attrType == GC_TYPE_LANGUAGE:
    gs_body[attrName] = getChoice(LANGUAGE_CODES_MAP, mapChoice=True)
  else: # GC_TYPE_INTEGER
    if attrName == u'maxMessageBytes':
      gs_body[attrName] = getMaxMessageBytes()
    else:
      gs_body[attrName] = getInteger()

def GroupIsAbuseOrPostmaster(emailAddr):
  return emailAddr.startswith(u'abuse@') or emailAddr.startswith(u'postmaster@')

def doCreateGroup():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  body = {u'email': getEmailAddress(noUid=True)}
  gs_body = {}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'name':
      body[u'name'] = getString(OB_STRING)
    elif myarg == u'description':
      body[u'description'] = getString(OB_STRING)
    else:
      getGroupAttrValue(myarg, gs_body)
  body.setdefault(u'name', body[u'email'])
  print u"Creating group %s" % body[u'email']
  callGAPI(cd.groups(), u'insert', body=body, fields=u'email')
  if gs_body and not GroupIsAbuseOrPostmaster(body[u'email']):
    gs = buildGAPIObject(GAPI_GROUPSSETTINGS_API)
    callGAPI(gs.groups(), u'patch', retry_reasons=[GAPI_SERVICE_LIMIT], groupUniqueId=body[u'email'], body=gs_body)

UPDATE_GROUP_SUBCMDS = [u'add', u'clear', u'delete', u'remove', u'sync', u'update']

GROUP_ROLES_MAP = {
  u'owner': ROLE_OWNER,
  u'owners': ROLE_OWNER,
  u'manager': ROLE_MANAGER,
  u'managers': ROLE_MANAGER,
  u'member': ROLE_MEMBER,
  u'members': ROLE_MEMBER,
  }

def doUpdateGroup():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  group = getEmailAddress()
  myarg = getChoice(UPDATE_GROUP_SUBCMDS, defaultChoice=None)
  if not myarg:
    body = {}
    gs_body = {}
    while CL_argvI < CL_argvLen:
      myarg = getArgument()
      if myarg == u'email':
        body[u'email'] = getEmailAddress(noUid=True)
      elif myarg == u'admincreated':
        body[u'adminCreated'] = getBoolean()
      else:
        getGroupAttrValue(myarg, gs_body)
    if body or (group.find(u'@') == -1): # group settings API won't take uid so we make sure cd API is used so that we can grab real email.
      cd_result = callGAPI(cd.groups(), u'patch', groupKey=group, body=body)
      group = cd_result[u'email']
    if gs_body and not GroupIsAbuseOrPostmaster(group):
      gs = buildGAPIObject(GAPI_GROUPSSETTINGS_API)
      callGAPI(gs.groups(), u'patch', retry_reasons=[GAPI_SERVICE_LIMIT], groupUniqueId=group, body=gs_body)
    print u'updated group %s' % group
  elif myarg == u'add':
    role = ROLE_MEMBER
    role = getChoice(GROUP_ROLES_MAP, defaultChoice=ROLE_MEMBER, mapChoice=True)
    checkNotSuspended = checkArgumentPresent(NOTSUSPENDED_ARGUMENT)
    _, users_email = getEntityToModify(checkNotSuspended=checkNotSuspended)
    checkForExtraneousArguments()
    for user_email in users_email:
      user_email = normalizeEmailAddressOrUID(user_email)
      if user_email.find(u'@') != -1:
        body = {u'role': role, u'email': user_email}
      else:
        body = {u'role': role, u'id': user_email}
      sys.stderr.write(u' adding %s %s...\n' % (role.lower(), user_email))
      try:
        callGAPI(cd.members(), u'insert', soft_errors=True, groupKey=group, body=body)
      except googleapiclient.errors.HttpError:
        pass
  elif myarg == u'sync':
    role = getChoice(GROUP_ROLES_MAP, defaultChoice=ROLE_MEMBER, mapChoice=True)
    body = {u'role': role}
    role = role.lower()
    checkNotSuspended = checkArgumentPresent(NOTSUSPENDED_ARGUMENT)
    _, users_email = getEntityToModify(checkNotSuspended=checkNotSuspended)
    checkForExtraneousArguments()
    users_email = [x.lower() for x in users_email]
    current_emails = getUsersToModify(u'group', group, member_type=role)
    current_emails = [x.lower() for x in current_emails]
    to_add = list(set(users_email) - set(current_emails))
    to_remove = list(set(current_emails) - set(users_email))
    sys.stderr.write(u'Need to add %s %s and remove %s.\n' % (len(to_add), role, len(to_remove)))
    items = []
    for user_email in to_add:
      items.append([GAM_CMD, u'update', u'group', group, u'add', role, user_email])
    for user_email in to_remove:
      items.append([GAM_CMD, u'update', u'group', group, u'remove', user_email])
    run_batch(items)
  elif myarg in [u'delete', u'remove']:
    role = getChoice(GROUP_ROLES_MAP, defaultChoice=ROLE_MEMBER, mapChoice=True)
    _, users_email = getEntityToModify()
    checkForExtraneousArguments()
    for user_email in users_email:
      user_email = normalizeEmailAddressOrUID(user_email)
      sys.stderr.write(u' removing %s\n' % user_email)
      callGAPI(cd.members(), u'delete', soft_errors=True, groupKey=group, memberKey=user_email)
  elif myarg == u'update':
    role = getChoice(GROUP_ROLES_MAP, defaultChoice=ROLE_MEMBER, mapChoice=True)
    body = {u'role': role}
    role = role.lower()
    _, users_email = getEntityToModify()
    checkForExtraneousArguments()
    for user_email in users_email:
      user_email = normalizeEmailAddressOrUID(user_email)
      sys.stderr.write(u' updating %s to %s...\n' % (user_email, role))
      try:
        callGAPI(cd.members(), u'update', soft_errors=True, groupKey=group, memberKey=user_email, body=body)
      except googleapiclient.errors.HttpError:
        pass
  else: # clear
    roleList = []
    while CL_argvI < CL_argvLen:
      roleList.append(getChoice(GROUP_ROLES_MAP, mapChoice=True))
    if roleList:
      roles = u','.join(sorted(set(roleList)))
    else:
      roles = ROLE_MEMBER
    user_emails = getUsersToModify(u'group', group, member_type=roles)
    for user_email in user_emails:
      sys.stderr.write(u' removing %s\n' % user_email)
      callGAPI(cd.members(), u'delete', soft_errors=True, groupKey=group, memberKey=user_email)

def doDeleteGroup():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  group = getEmailAddress()
  checkForExtraneousArguments()
  print u"Deleting group %s" % group
  callGAPI(cd.groups(), u'delete', groupKey=group)

GROUP_ARGUMENT_TO_PROPERTY_TITLE_MAP = {
  u'admincreated': [u'adminCreated', u'Admin_Created'],
  u'aliases': [u'aliases', u'Aliases', u'nonEditableAliases', u'NonEditableAliases'],
  u'description': [u'description', u'Description'],
  u'email': [u'email', u'Email'],
  u'id': [u'id', u'ID'],
  u'name': [u'name', u'Name'],
  }

INFO_GROUP_OPTIONS = [u'nousers', u'groups',]

def doInfoGroup(group_name=None):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  getAliases = getUsers = True
  getGroups = getSettings = False
  cdfieldsList = gsfieldsList = None
  settings = {}
  if group_name is None:
    group_name = getEmailAddress()
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'nousers':
      getUsers = False
    elif myarg == u'noaliases':
      getAliases = False
    elif myarg == u'groups':
      getGroups = True
    elif myarg in GROUP_ARGUMENT_TO_PROPERTY_TITLE_MAP:
      if not cdfieldsList:
        cdfieldsList = [u'email',]
      cdfieldsList.extend([GROUP_ARGUMENT_TO_PROPERTY_TITLE_MAP[myarg][0],])
    elif myarg in GROUP_ATTRIBUTES:
      if not gsfieldsList:
        gsfieldsList = []
      gsfieldsList.extend([GROUP_ATTRIBUTES[myarg][0],])
    elif myarg == u'fields':
      if not cdfieldsList:
        cdfieldsList = [u'email',]
      if not gsfieldsList:
        gsfieldsList = []
      fieldNameList = getString(OB_FIELD_NAME_LIST)
      for field in fieldNameList.lower().replace(u',', u' ').split():
        if field in GROUP_ARGUMENT_TO_PROPERTY_TITLE_MAP:
          cdfieldsList.extend([GROUP_ARGUMENT_TO_PROPERTY_TITLE_MAP[field][0],])
        elif field in GROUP_ATTRIBUTES:
          gsfieldsList.extend([GROUP_ATTRIBUTES[field][0],])
        else:
          putArgumentBack()
          invalidChoiceExit(GROUP_ARGUMENT_TO_PROPERTY_TITLE_MAP.keys()+GROUP_ATTRIBUTES.keys())
    elif myarg in INFO_USER_OPTIONS:
      if myarg == u'schemas':
        getString(OB_SCHEMA_NAME_LIST)
    else:
      unknownArgumentExit()
  if cdfieldsList:
    cdfields = u','.join(set(cdfieldsList))
  else:
    cdfields = None
  if gsfieldsList is None:
    getSettings = True
    gsfields = None
  elif gsfieldsList:
    getSettings = True
    gsfields = u','.join(set(gsfieldsList))
  else:
    gsfields = None
  basic_info = callGAPI(cd.groups(), u'get', groupKey=group_name, fields=cdfields)
  if getSettings and not GroupIsAbuseOrPostmaster(basic_info[u'email']):
    gs = buildGAPIObject(GAPI_GROUPSSETTINGS_API)
    try:
      settings = callGAPI(gs.groups(), u'get', throw_reasons=[GAPI_AUTH_ERROR], retry_reasons=[GAPI_SERVICE_LIMIT],
                          groupUniqueId=basic_info[u'email'], fields=gsfields) # Use email address retrieved from cd since GS API doesn't support uid
    except GAPI_authError:
      pass
  print u'Group: {0}'.format(group_name)
  print u'Group Settings:'
  for key, value in basic_info.items():
    if (key in [u'kind', u'etag']) or ((key == u'aliases') and (not getAliases)):
      continue
    if isinstance(value, list):
      print u' %s:' % key
      for val in value:
        print u'  %s' % val
    else:
      print convertUTF8(u' %s: %s' % (key, value))
  try:
    for key, value in settings.items():
      if key in [u'kind', u'etag', u'description', u'email', u'name']:
        continue
      if key == u'maxMessageBytes':
        if value > 1024*1024:
          value = u'%sM' % (value / 1024 / 1024)
        elif value > 1024:
          value = u'%sK' % (value / 1024)
      elif key == u'customFooterText':
        value = value.replace(u'\n', u'\\n')
      print u' %s: %s' % (key, value)
  except UnboundLocalError:
    pass
  if getGroups:
    groups = callGAPIpages(cd.groups(), u'list', u'groups',
                           userKey=basic_info[u'email'], fields=u'nextPageToken,groups(name,email)')
    if groups:
      print u'Groups: ({0})'.format(len(groups))
      for groupm in groups:
        print u'  %s: %s' % (groupm[u'name'], groupm[u'email'])
  if getUsers:
    members = callGAPIpages(cd.members(), u'list', u'members',
                            groupKey=group_name, fields=u'nextPageToken,members(email,id,role,type)', maxResults=GC_Values[GC_MEMBER_MAX_RESULTS])
    print u'Members:'
    for member in members:
      try:
        print u' %s: %s (%s)' % (member[u'role'].lower(), member[u'email'], member[u'type'].lower())
      except KeyError:
        try:
          print u' member: %s (%s)' % (member[u'email'], member[u'type'].lower())
        except KeyError:
          print u' member: %s (%s)' % (member[u'id'], member[u'type'].lower())
    print u'Total %s users in group' % len(members)

def doPrintGroups():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  getSettings = sortHeaders = False
  customer = GC_Values[GC_CUSTOMER_ID]
  usedomain = usemember = None
  convertCRNL = GC_Values[GC_CSV_OUTPUT_CONVERT_CR_NL]
  delimiter = GC_Values[GC_CSV_OUTPUT_FIELD_DELIMITER]
  members = membersCountOnly = managers = managersCountOnly = owners = ownersCountOnly = False
  todrive = False
  cdfieldsList = []
  gsfieldsList = []
  fieldsTitles = {}
  titles = []
  csvRows = []
  addFieldTitleToCSVfile(u'email', GROUP_ARGUMENT_TO_PROPERTY_TITLE_MAP, cdfieldsList, fieldsTitles, titles)
  maxResults = None
  roleList = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'todrive':
      todrive = True
    elif myarg == u'domain':
      usedomain = getString(OB_DOMAIN_NAME).lower()
      customer = None
    elif myarg == u'member':
      usemember = getEmailAddress()
      customer = None
    elif myarg == u'maxresults':
      maxResults = getInteger(minVal=1)
    elif myarg in [u'convertcrnl', u'converttextnl', u'convertfooternl']:
      convertCRNL = True
    elif myarg == u'delimiter':
      delimiter = getString(OB_STRING, minLen=1, maxLen=1)
    elif myarg == u'allfields':
      getSettings = sortHeaders = True
      cdfieldsList = []
      gsfieldsList = []
      fieldsTitles = {}
      for field in GROUP_ARGUMENT_TO_PROPERTY_TITLE_MAP:
        addFieldTitleToCSVfile(field, GROUP_ARGUMENT_TO_PROPERTY_TITLE_MAP, cdfieldsList, fieldsTitles, titles)
    elif myarg in GROUP_ARGUMENT_TO_PROPERTY_TITLE_MAP:
      addFieldTitleToCSVfile(myarg, GROUP_ARGUMENT_TO_PROPERTY_TITLE_MAP, cdfieldsList, fieldsTitles, titles)
    elif myarg in GROUP_ATTRIBUTES:
      addFieldToCSVfile(myarg, {myarg: [GROUP_ATTRIBUTES[myarg][0]]}, gsfieldsList, fieldsTitles, titles)
    elif myarg == u'fields':
      fieldNameList = getString(OB_FIELD_NAME_LIST)
      for field in fieldNameList.lower().replace(u',', u' ').split():
        if field in GROUP_ARGUMENT_TO_PROPERTY_TITLE_MAP:
          addFieldTitleToCSVfile(field, GROUP_ARGUMENT_TO_PROPERTY_TITLE_MAP, cdfieldsList, fieldsTitles, titles)
        elif field in GROUP_ATTRIBUTES:
          addFieldToCSVfile(field, {field: [GROUP_ATTRIBUTES[field][0]]}, gsfieldsList, fieldsTitles, titles)
        else:
          putArgumentBack()
          invalidChoiceExit(GROUP_ARGUMENT_TO_PROPERTY_TITLE_MAP.keys()+GROUP_ATTRIBUTES.keys())
    elif myarg in [u'members', u'memberscount']:
      roleList.append(ROLE_MEMBER)
      addTitlesToCSVfile([u'Members',], titles)
      members = True
      if myarg == u'memberscount':
        membersCountOnly = True
    elif myarg in [u'managers', u'managerscount']:
      roleList.append(ROLE_MANAGER)
      addTitlesToCSVfile([u'Managers',], titles)
      managers = True
      if myarg == u'managerscount':
        managersCountOnly = True
    elif myarg in [u'owners', u'ownerscount']:
      roleList.append(ROLE_OWNER)
      addTitlesToCSVfile([u'Owners',], titles)
      owners = True
      if myarg == u'ownerscount':
        ownersCountOnly = True
    elif myarg == u'countsonly':
      membersCountOnly = managersCountOnly = ownersCountOnly = True
    elif myarg == u'settings':
      getSettings = True
    else:
      unknownArgumentExit()
  if cdfieldsList:
    cdfields = u'nextPageToken,groups({0})'.format(u','.join(set(cdfieldsList)))
  else:
    cdfields = None
  if gsfieldsList:
    getSettings = True
    gsfields = u','.join(set(gsfieldsList))
  elif getSettings:
    gsfields = None
  if getSettings:
    gs = buildGAPIObject(GAPI_GROUPSSETTINGS_API)
  roles = u','.join(sorted(set(roleList)))
  sys.stderr.write(u"Retrieving All Groups for G Suite account (may take some time on a large account)...\n")
  page_message = u'Got %%num_items%% groups: %%first_item%% - %%last_item%%\n'
  entityList = callGAPIpages(cd.groups(), u'list', u'groups',
                             page_message=page_message, message_attribute=u'email',
                             customer=customer, domain=usedomain, userKey=usemember,
                             fields=cdfields, maxResults=maxResults)
  i = 0
  count = len(entityList)
  for groupEntity in entityList:
    i += 1
    groupEmail = groupEntity[u'email']
    row = {}
    for field in cdfieldsList:
      if field in groupEntity:
        if isinstance(groupEntity[field], list):
          row[fieldsTitles[field]] = delimiter.join(groupEntity[field])
        elif convertCRNL and field in GROUP_FIELDS_WITH_CRS_NLS:
          row[fieldsTitles[field]] = convertCRsNLs(groupEntity[field])
        else:
          row[fieldsTitles[field]] = groupEntity[field]
    if roles:
      sys.stderr.write(u' Getting %s for %s%s' % (roles, groupEmail, currentCountNL(i, count)))
      page_message = u'Got %%num_items%% members: %%first_item%% - %%last_item%%\n'
      groupMembers = callGAPIpages(cd.members(), u'list', u'members',
                                   page_message=page_message, message_attribute=u'email',
                                   groupKey=groupEmail, roles=roles, fields=u'nextPageToken,members(email,id,role)', maxResults=GC_Values[GC_MEMBER_MAX_RESULTS])
      if members:
        membersList = []
        membersCount = 0
      if managers:
        managersList = []
        managersCount = 0
      if owners:
        ownersList = []
        ownersCount = 0
      for member in groupMembers:
        member_email = member.get(u'email', member.get(u'id', None))
        if not member_email:
          sys.stderr.write(u' Not sure what to do with: %s' % member)
          continue
        role = member.get(u'role', ROLE_MEMBER)
        if role == ROLE_MEMBER:
          if members:
            membersCount += 1
            if not membersCountOnly:
              membersList.append(member_email)
        elif role == ROLE_MANAGER:
          if managers:
            managersCount += 1
            if not managersCountOnly:
              managersList.append(member_email)
        elif role == ROLE_OWNER:
          if owners:
            ownersCount += 1
            if not ownersCountOnly:
              ownersList.append(member_email)
        elif members:
          membersCount += 1
          if not membersCountOnly:
            membersList.append(member_email)
      if members:
        row[u'Members'] = membersCount if membersCountOnly else delimiter.join(membersList)
      if managers:
        row[u'Managers'] = managersCount if managersCountOnly else delimiter.join(managersList)
      if owners:
        row[u'Owners'] = ownersCount if ownersCountOnly else delimiter.join(ownersList)
    if getSettings and not GroupIsAbuseOrPostmaster(groupEmail):
      sys.stderr.write(u" Retrieving Settings for group %s%s...\r\n" % (groupEmail, currentCount(i, count)))
      settings = callGAPI(gs.groups(), u'get',
                          soft_errors=True,
                          retry_reasons=[GAPI_SERVICE_LIMIT, GAPI_INVALID],
                          groupUniqueId=groupEmail, fields=gsfields)
      if settings:
        for key in settings:
          if key in [u'email', u'name', u'description', u'kind', u'etag']:
            continue
          setting_value = settings[key]
          if setting_value is None:
            setting_value = u''
          if key not in titles:
            addTitleToCSVfile(key, titles)
          if convertCRNL and key in GROUP_FIELDS_WITH_CRS_NLS:
            row[key] = convertCRsNLs(setting_value)
          else:
            row[key] = setting_value
      else:
        sys.stderr.write(u" Settings unavailable for group %s (%s/%s)...\r\n" % (groupEmail, i, count))
    csvRows.append(row)
  if sortHeaders:
    sortCSVTitles([u'Email',], titles)
  writeCSVfile(csvRows, titles, u'Groups', todrive)

def getGroupMembers(cd, groupEmail, membersList, membersSet, i, count, noduplicates, recursive, level):
  try:
    sys.stderr.write(u'Getting members for %s%s' % (groupEmail, currentCountNL(i, count)))
    groupMembers = callGAPIpages(cd.members(), u'list', u'members',
                                 throw_reasons=[GAPI_GROUP_NOT_FOUND, GAPI_DOMAIN_NOT_FOUND, GAPI_FORBIDDEN],
                                 groupKey=groupEmail, maxResults=GC_Values[GC_MEMBER_MAX_RESULTS])
    if not recursive:
      if noduplicates:
        for member in groupMembers:
          if member[u'id'] in membersSet:
            continue
          membersSet.add(member[u'id'])
          membersList.append(member)
      else:
        membersList.extend(groupMembers)
    else:
      for member in groupMembers:
        if member[u'type'] == u'USER':
          if noduplicates:
            if member[u'id'] in membersSet:
              continue
            membersSet.add(member[u'id'])
          member[u'level'] = level
          member[u'subgroup'] = groupEmail
          membersList.append(member)
        else:
          getGroupMembers(cd, member[u'email'], membersList, membersSet, i, count, noduplicates, recursive, level+1)
  except (GAPI_groupNotFound, GAPI_domainNotFound, GAPI_forbidden):
    entityUnknownWarning(u'Group', groupEmail, i, count)

GROUPMEMBERS_FIELD_NAMES_MAP = {
  u'email': u'email',
  u'groupemail': u'group',
  u'id': u'id',
  u'name': u'name',
  u'role': u'role',
  u'status': u'status',
  u'type': u'type',
  u'useremail': u'email',
  }

GROUPMEMBERS_DEFAULT_FIELDS = [u'id', u'role', u'group', u'email', u'type', u'status']

def doPrintGroupMembers():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  todrive = groupname = membernames = noduplicates = recursive = False
  customer = GC_Values[GC_CUSTOMER_ID]
  domain = usemember = None
  fieldsList = []
  fieldsTitles = {}
  titles = []
  csvRows = []
  groups_to_get = []
  userFieldsList = []
  userFieldsTitles = {}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'todrive':
      todrive = True
    elif myarg == u'domain':
      domain = getString(OB_DOMAIN_NAME).lower()
      customer = None
    elif myarg == u'member':
      usemember = getEmailAddress()
      customer = None
    elif myarg == u'group':
      group_email = getEmailAddress()
      groups_to_get = [{u'email': group_email}]
    elif myarg in GROUPMEMBERS_FIELD_NAMES_MAP:
      myarg = GROUPMEMBERS_FIELD_NAMES_MAP[myarg]
      addFieldToCSVfile(myarg, {myarg: [myarg]}, fieldsList, fieldsTitles, titles)
    elif myarg == u'fields':
      fieldNameList = getString(OB_FIELD_NAME_LIST)
      for field in fieldNameList.lower().replace(u',', u' ').split():
        if field in GROUPMEMBERS_FIELD_NAMES_MAP:
          field = GROUPMEMBERS_FIELD_NAMES_MAP[field]
          addFieldToCSVfile(field, {field: [field]}, fieldsList, fieldsTitles, titles)
        else:
          putArgumentBack()
          invalidChoiceExit(GROUPMEMBERS_FIELD_NAMES_MAP)
    elif myarg == u'membernames':
      membernames = True
    elif myarg == u'userfields':
      fieldNameList = getString(OB_FIELD_NAME_LIST)
      for field in fieldNameList.lower().replace(u',', u' ').split():
        if field in USER_ARGUMENT_TO_PROPERTY_MAP:
          addFieldToCSVfile(field, USER_ARGUMENT_TO_PROPERTY_MAP, userFieldsList, userFieldsTitles, titles)
        else:
          putArgumentBack()
          invalidChoiceExit(USER_ARGUMENT_TO_PROPERTY_MAP)
    elif myarg == u'noduplicates':
      noduplicates = True
    elif myarg == u'recursive':
      recursive = True
    else:
      unknownArgumentExit()
  if not fieldsList:
    for field in GROUPMEMBERS_DEFAULT_FIELDS:
      addFieldToCSVfile(field, {field: [field]}, fieldsList, fieldsTitles, titles)
  else:
    if u'name'in fieldsList:
      membernames = True
      fieldsList.remove(u'name')
  if u'group' in fieldsList:
    groupname = True
    fieldsList.remove(u'group')
  if userFieldsList:
    if not membernames and u'name.fullName' in userFieldsList:
      membernames = True
  if membernames:
    if u'name.fullName' not in userFieldsList:
      userFieldsList.append(u'name.fullName')
    addTitlesToCSVfile([u'name'], titles)
    removeTitlesFromCSVfile([u'name.fullName'], titles)
  if userFieldsList:
    userFields = u','.join(set(userFieldsList)).replace(u'.', u'/')
  else:
    userFields = None
  if not groups_to_get:
    groups_to_get = callGAPIpages(cd.groups(), u'list', u'groups', message_attribute=u'email',
                                  customer=customer, domain=domain, userKey=usemember, fields=u'nextPageToken,groups(email)')
  membersSet = set()
  level = 0
  i = 0
  count = len(groups_to_get)
  for group in groups_to_get:
    i += 1
    groupEmail = group[u'email']
    membersList = []
    getGroupMembers(cd, groupEmail, membersList, membersSet, i, count, noduplicates, recursive, level)
    for member in membersList:
      row = {}
      if groupname:
        row[u'group'] = groupEmail
      for title in fieldsList:
        row[title] = member[title]
      if recursive:
        row[u'level'] = member[u'level']
        row[u'subgroup'] = member[u'subgroup']
      if userFieldsList:
        if membernames:
          row[u'name'] = u'Unknown'
        memberType = member.get(u'type')
        if memberType == u'USER':
          try:
            mbinfo = callGAPI(cd.users(), u'get',
                              throw_reasons=[GAPI_USER_NOT_FOUND, GAPI_FORBIDDEN],
                              userKey=member[u'id'], fields=userFields)
            if membernames:
              row[u'name'] = mbinfo[u'name'][u'fullName']
              del mbinfo[u'name'][u'fullName']
            addRowTitlesToCSVfile(flattenJSON(mbinfo, flattened=row), csvRows, titles)
          except (GAPI_userNotFound, GAPI_forbidden):
            csvRows.append(row)
        else:
          if membernames and memberType == u'GROUP':
            try:
              mbinfo = callGAPI(cd.groups(), u'get',
                                throw_reasons=[GAPI_GROUP_NOT_FOUND, GAPI_FORBIDDEN],
                                groupKey=member[u'id'], fields=u'name')
              row[u'name'] = mbinfo[u'name']
            except (GAPI_groupNotFound, GAPI_forbidden):
              pass
          csvRows.append(row)
      else:
        csvRows.append(row)
  sortCSVTitles(GROUPMEMBERS_DEFAULT_FIELDS, titles)
  if recursive:
    removeTitlesFromCSVfile([u'level', u'subgroup'], titles)
    addTitlesToCSVfile([u'level', u'subgroup'], titles)
  writeCSVfile(csvRows, titles, u'Group Members', todrive)

def doPrintLicenses(return_list=False, skus=None):
  lic = buildGAPIObject(GAPI_LICENSING_API)
  products = [u'Google-Apps', u'Google-Vault']
  feed = collections.deque()
  titles = [u'userId', u'productId', u'skuId']
  csvRows = []
  todrive = False
  if not return_list:
    while CL_argvI < CL_argvLen:
      myarg = getArgument()
      if myarg == u'todrive':
        todrive = True
      elif myarg in [u'products', u'product']:
        products = getGoogleProductListMap()
        skus = []
      elif myarg in [u'sku', u'skus']:
        skus = getGoogleSKUListMap()
        products = []
      else:
        unknownArgumentExit()
  if skus:
    for skuId in skus:
      page_message = u'Got %%%%total_items%%%% Licenses for %s...\n' % skuId
      try:
        feed += callGAPIpages(lic.licenseAssignments(), u'listForProductAndSku', u'items', page_message=page_message, throw_reasons=[GAPI_INVALID, GAPI_FORBIDDEN],
                              customerId=GC_Values[GC_DOMAIN], productId=GOOGLE_SKUS[skuId], skuId=skuId, fields=u'items(productId,skuId,userId),nextPageToken')
      except (GAPI_invalid, GAPI_forbidden):
        pass
  else:
    for productId in products:
      page_message = u'Got %%%%total_items%%%% Licenses for %s...\n' % productId
      try:
        feed += callGAPIpages(lic.licenseAssignments(), u'listForProduct', u'items', page_message=page_message, throw_reasons=[GAPI_INVALID, GAPI_FORBIDDEN],
                              customerId=GC_Values[GC_DOMAIN], productId=productId, fields=u'items(productId,skuId,userId),nextPageToken')
      except (GAPI_invalid, GAPI_forbidden):
        pass
  while feed:
    u_license = feed.popleft()
    row = {}
    for title in u_license:
      if title in [u'kind', u'etags', u'selfLink']:
        continue
      if title not in titles:
        titles.append(title)
      row[title] = u_license[title]
    csvRows.append(row)
  if return_list:
    return csvRows
  writeCSVfile(csvRows, titles, u'Licenses', todrive)

def doUpdateNotification():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  notificationIds = []
  get_all = False
  isUnread = None
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'unread':
      isUnread = True
      mark_as = u'unread'
    elif myarg == u'read':
      isUnread = False
      mark_as = u'read'
    elif myarg == u'id':
      notificationId = getString(OB_NOTIFICATION_ID)
      if notificationId.lower() == u'all':
        get_all = True
      else:
        notificationIds.append(notificationId)
    else:
      unknownArgumentExit()
  if isUnread is None:
    missingChoiceExit([u'unread', u'read'])
  if get_all:
    notifications = callGAPIpages(cd.notifications(), u'list', u'items',
                                  customer=GC_Values[GC_CUSTOMER_ID], fields=u'items(notificationId,isUnread),nextPageToken')
    for noti in notifications:
      if noti[u'isUnread'] != isUnread:
        notificationIds.append(noti[u'notificationId'])
  print u'Marking %s notification(s) as %s...' % (len(notificationIds), mark_as)
  for notificationId in notificationIds:
    result = callGAPI(cd.notifications(), u'patch',
                      customer=GC_Values[GC_CUSTOMER_ID], notificationId=notificationId, body={u'isUnread': isUnread}, fields=u'notificationId,isUnread')
    if result[u'isUnread']:
      read_result = u'unread'
    else:
      read_result = u'read'
    print u'marked %s as %s' % (result[u'notificationId'], read_result)

def doDeleteNotification():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  notificationIds = []
  get_all = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'id':
      notificationId = getString(OB_NOTIFICATION_ID)
      if notificationId.lower() == u'all':
        get_all = True
      else:
        notificationIds.append(notificationId)
    else:
      unknownArgumentExit()
  if get_all:
    notifications = callGAPIpages(cd.notifications(), u'list', u'items',
                                  customer=GC_Values[GC_CUSTOMER_ID], fields=u'items(notificationId),nextPageToken')
    for noti in notifications:
      notificationIds.append(noti[u'notificationId'])
  print u'Deleting %s notification(s)...' % len(notificationIds)
  for notificationId in notificationIds:
    callGAPI(cd.notifications(), u'delete',
             customer=GC_Values[GC_CUSTOMER_ID], notificationId=notificationId)
    print u'deleted %s' % id

def doInfoNotifications():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  unread_only = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'unreadonly':
      unread_only = True
    else:
      unknownArgumentExit()
  notifications = callGAPIpages(cd.notifications(), u'list', u'items', customer=GC_Values[GC_CUSTOMER_ID])
  for notification in notifications:
    if unread_only and not notification[u'isUnread']:
      continue
    print u'From: %s' % notification[u'fromAddress']
    print u'Subject: %s' % notification[u'subject']
    print u'Date: %s' % notification[u'sendTime']
    print u'ID: %s' % notification[u'notificationId']
    print u'Read Status: %s' % ([u'READ', u'UNREAD'][notification[u'isUnread']])
    print u''
    print convertUTF8(dehtml(notification[u'body']))
    print u''
    print u'--------------'
    print u''

def doCreateResourceCalendar():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  body = {u'resourceId': getString(OB_RESOURCE_ID),
          u'resourceName': getString(OB_NAME)}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'description':
      body[u'resourceDescription'] = getString(OB_STRING)
    elif myarg == u'type':
      body[u'resourceType'] = getString(OB_STRING)
    else:
      unknownArgumentExit()
  print u'Creating resource %s...' % body[u'resourceId']
  callGAPI(cd.resources().calendars(), u'insert',
           customer=GC_Values[GC_CUSTOMER_ID], body=body)

def doUpdateResourceCalendar():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  resId = getString(OB_RESOURCE_ID)
  body = {}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'name':
      body[u'resourceName'] = getString(OB_STRING)
    elif myarg == u'description':
      body[u'resourceDescription'] = getString(OB_STRING)
    elif myarg == u'type':
      body[u'resourceType'] = getString(OB_STRING)
    else:
      unknownArgumentExit()
  # Use patch since it seems to work better.
  # update requires name to be set.
  callGAPI(cd.resources().calendars(), u'patch',
           customer=GC_Values[GC_CUSTOMER_ID], calendarResourceId=resId, body=body,
           fields=u'')
  print u'updated resource %s' % resId

def doDeleteResourceCalendar():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  resId = getString(OB_RESOURCE_ID)
  checkForExtraneousArguments()
  print u"Deleting resource calendar %s" % resId
  callGAPI(cd.resources().calendars(), u'delete',
           customer=GC_Values[GC_CUSTOMER_ID], calendarResourceId=resId)

def doInfoResourceCalendar():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  resId = getString(OB_RESOURCE_ID)
  checkForExtraneousArguments()
  resource = callGAPI(cd.resources().calendars(), u'get',
                      customer=GC_Values[GC_CUSTOMER_ID], calendarResourceId=resId)
  for key, value in resource.items():
    if key in [u'kind', u'etag', u'etags']:
      continue
    print u'%s: %s' % (key, value)

RESCAL_DFLTFIELDS = [u'id', u'name', u'email',]
RESCAL_ALLFIELDS = [u'id', u'name', u'email', u'description', u'type',]

RESCAL_ARGUMENT_TO_PROPERTY_MAP = {
  u'description': [u'resourceDescription'],
  u'email': [u'resourceEmail'],
  u'id': [u'resourceId'],
  u'name': [u'resourceName'],
  u'type': [u'resourceType'],
  }

RESOURCE_FIELDS_WITH_CRS_NLS = [u'resourceDescription']

def doPrintResourceCalendars():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  convertCRNL = GC_Values[GC_CSV_OUTPUT_CONVERT_CR_NL]
  todrive = False
  fieldsList = []
  fieldsTitles = {}
  titles = []
  csvRows = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'todrive':
      todrive = True
    elif myarg == u'allfields':
      fieldsList = []
      fieldsTitles = {}
      titles = []
      for field in RESCAL_ALLFIELDS:
        addFieldToCSVfile(field, RESCAL_ARGUMENT_TO_PROPERTY_MAP, fieldsList, fieldsTitles, titles)
    elif myarg in RESCAL_ARGUMENT_TO_PROPERTY_MAP:
      addFieldToCSVfile(myarg, RESCAL_ARGUMENT_TO_PROPERTY_MAP, fieldsList, fieldsTitles, titles)
    elif myarg in [u'convertcrnl', u'converttextnl']:
      convertCRNL = True
    else:
      unknownArgumentExit()
  if not fieldsList:
    for field in RESCAL_DFLTFIELDS:
      addFieldToCSVfile(field, RESCAL_ARGUMENT_TO_PROPERTY_MAP, fieldsList, fieldsTitles, titles)
  sys.stderr.write(u"Retrieving All Resource Calendars for your account (may take some time on a large domain)\n")
  page_message = u'Got %%total_items%% resources: %%first_item%% - %%last_item%%\n'
  resources = callGAPIpages(cd.resources().calendars(), u'list', u'items',
                            page_message=page_message, message_attribute=u'resourceId',
                            customer=GC_Values[GC_CUSTOMER_ID], fields=u'nextPageToken,items({0})'.format(u','.join(set(fieldsList))))
  for resource in resources:
    row = {}
    for field in fieldsList:
      if convertCRNL and field in RESOURCE_FIELDS_WITH_CRS_NLS:
        row[fieldsTitles[field]] = convertCRsNLs(resource.get(field, u''))
      else:
        row[fieldsTitles[field]] = resource.get(field, u'')
    csvRows.append(row)
  writeCSVfile(csvRows, titles, u'Resources', todrive)

VALIDEMAIL_PATTERN = re.compile(r'^[^@]+@[^@]+\.[^@]+$')

def getValidateLoginHint(login_hint):
  if login_hint:
    login_hint = login_hint.strip()
    if VALIDEMAIL_PATTERN.match(login_hint):
      return login_hint
  while True:
    login_hint = raw_input(u'\nWhat is your G Suite admin email address? ').strip()
    if VALIDEMAIL_PATTERN.match(login_hint):
      return login_hint
    print u'Error: that is not a valid email address'

def getCRMService(login_hint):
  from oauth2client.contrib.dictionary_storage import DictionaryStorage
  login_hint = getValidateLoginHint(login_hint)
  scope = u'https://www.googleapis.com/auth/cloud-platform'
  client_id = u'297408095146-fug707qsjv4ikron0hugpevbrjhkmsk7.apps.googleusercontent.com'
  client_secret = u'qM3dP8f_4qedwzWQE1VR4zzU'
  flow = oauth2client.client.OAuth2WebServerFlow(client_id=client_id,
                                                 client_secret=client_secret, scope=scope, redirect_uri=oauth2client.client.OOB_CALLBACK_URN,
                                                 user_agent=GAM_INFO, access_type=u'online', response_type=u'code', login_hint=login_hint)
  storage_dict = {}
  storage = DictionaryStorage(storage_dict, u'credentials')
  flags = cmd_flags(noLocalWebserver=GC_Values[GC_NO_BROWSER])
  http = httplib2.Http(disable_ssl_certificate_validation=GC_Values[GC_NO_VERIFY_SSL])
  try:
    credentials = oauth2client.tools.run_flow(flow=flow, storage=storage, flags=flags, http=http)
  except httplib2.CertificateValidationUnsupported:
    noPythonSSLExit()
  credentials.user_agent = GAM_INFO
  http = credentials.authorize(httplib2.Http(disable_ssl_certificate_validation=GC_Values[GC_NO_VERIFY_SSL],
                                             cache=GC_Values[GC_CACHE_DIR]))
  return (googleapiclient.discovery.build(u'cloudresourcemanager', u'v1', http=http, cache_discovery=False), http)

def doCreateProject():
  login_hint = getEmailAddress(noUid=True, optional=True)
  checkForExtraneousArguments()
  crm, http = getCRMService(login_hint)
  project_id = u'gam-project'
  for i in range(3):
    project_id += u'-%s' % ''.join(random.choice(string.digits + string.ascii_lowercase) for i in range(3))
  project_name = u'project:%s' % project_id
  body = {u'projectId': project_id, u'name': u'GAM Project'}
  while True:
    create_again = False
    print u'Creating project "%s"...' % body[u'name']
    create_operation = callGAPI(crm.projects(), u'create', body=body)
    operation_name = create_operation[u'name']
    time.sleep(5) # Google recommends always waiting at least 5 seconds
    for i in range(1, 5):
      print u'Checking project status...'
      status = callGAPI(crm.operations(), u'get', name=operation_name)
      if u'error' in status:
        if u'message' in status[u'error'] and status[u'error'][u'message'].find(u'Callers must accept ToS') != -1:
          print u'''Please go to:

https://console.developers.google.com

and accept the Terms of Service (ToS). As soon as you've accepted the ToS popup, you can return here and press enter.'''
          raw_input()
          create_again = True
          break
        else:
          print status
          sys.exit(1)
      if u'done' in status and status[u'done']:
        break
      sleep_time = i ** 2
      print u'Project still being created. Sleeping %s seconds' % sleep_time
      time.sleep(sleep_time)
    if create_again:
      continue
    if not u'done' in status or not status[u'done']:
      print u'Failed to create project: %s' % status
      sys.exit(1)
    elif u'error' in status:
      print status[u'error']
      sys.exit(2)
    break

  serveman = googleapiclient.discovery.build(u'servicemanagement', u'v1', http=http, cache_discovery=False)
  apis = [u'admin-json.googleapis.com', u'appsactivity-json.googleapis.com', u'audit-json.googleapis.com'
          u'calendar-json.googleapis.com', u'classroom.googleapis.com', u'contacts-json.googleapis.com',
          u'drive', u'gmail-json.googleapis.com', u'groupssettings-json.googleapis.com',
          u'licensing-json.googleapis.com', u'plus-json.googleapis.com', u'siteverification-json.googleapis.com']
  for api in apis:
    while True:
      print u' enabling API %s...' % api
      try:
        callGAPI(serveman.services(), u'enable',
                 throw_reasons=[GAPI_FAILED_PRECONDITION],
                 serviceName=api, body={u'consumerId': project_name})
        break
      except GAPI_failedPrecondition as e:
        print u'\nThere was an error enabling %s. Please resolve error as described below:' % api
        print
        print u'\n%s\n' % e
        print
        raw_input(u'Press enter once resolved and we will try enabling the API again.')
  iam = googleapiclient.discovery.build(u'iam', u'v1', http=http, cache_discovery=False)
  print u'Creating Service Account'
  service_account = callGAPI(iam.projects().serviceAccounts(), u'create', name=u'projects/%s' % project_id,
                             body={u'accountId': project_id, u'serviceAccount': {u'displayName': u'GAM Project'}})
  body = {u'privateKeyType': u'TYPE_GOOGLE_CREDENTIALS_FILE', u'keyAlgorithm': u'KEY_ALG_RSA_4096'}
  key = callGAPI(iam.projects().serviceAccounts().keys(), u'create', name=service_account[u'name'], body=body)
  oauth2service_data = base64.b64decode(key[u'privateKeyData'])
  service_account_file = GC_Values[GC_OAUTH2SERVICE_JSON]
  if os.path.isfile(service_account_file):
    service_account_file = u'%s-%s' % (service_account_file, project_id)
  writeFile(service_account_file, oauth2service_data, continueOnError=False)
  console_credentials_url = u'https://console.developers.google.com/apis/credentials?project=%s' % project_id
  print u'''Please go to:

%s

1. Click the blue "Create credentials" button. Choose "OAuth client ID".
2. Click the blue "Configure consent screen" button. Enter "GAM" for "Product name to show to users".
3. Leave other fields blank. Click "Save" button.
3. Choose "Other" and click the blue "Create" button.
4. Copy your "client ID" value.

''' % console_credentials_url
  client_id = raw_input(u'Enter your Client ID: ')
  print u'\nNow go back to your browser and copy your client secret.'
  client_secret = raw_input(u'Enter your Client Secret: ')
  cs_data = u'''{
    "installed": {
        "auth_provider_x509_cert_url": "https://www.googleapis.com/oauth2/v1/certs",
        "auth_uri": "https://accounts.google.com/o/oauth2/auth",
        "client_id": "%s",
        "client_secret": "%s",
        "project_id": "%s",
        "redirect_uris": [
            "urn:ietf:wg:oauth:2.0:oob",
            "http://localhost"
        ],
        "token_uri": "https://accounts.google.com/o/oauth2/token"
    }
}''' % (client_id, client_secret, project_id)
  client_secrets_file = GC_Values[GC_CLIENT_SECRETS_JSON]
  if os.path.isfile(client_secrets_file):
    client_secrets_file = u'%s-%s' % (client_secrets_file, project_id)
  writeFile(client_secrets_file, cs_data, continueOnError=False)
  print u'''Almost there! Now please switch back to your browser and:

1. Click OK to close "OAuth client" popup if it's still open.
2. Click "Manage service accounts" on the right of the screen.
3. Click the 3 dots to the right of your service account.
4. Choose Edit.
5. Check the "Enable G Suite Domain-wide Delegation" box and click Save.
'''
  raw_input(u'Press Enter when done...')
  print u'That\'s it! Your GAM Project is created and ready to use.'

def doDeleteProjects():
  # Leave undocumented. Most users should never need.
  # Deletes all projects with ID gam-project-*
  login_hint = getEmailAddress(noUid=True, optional=True)
  checkForExtraneousArguments()
  crm, _ = getCRMService(login_hint)
  projects = callGAPIpages(crm.projects(), u'list', items=u'projects')
  for project in projects:
    pid = project[u'projectId']
    if pid.startswith(u'gam-project-'):
      print u'Deleting %s...' % pid
      try:
        callGAPI(crm.projects(), u'delete',
                 throw_reasons=[GAPI_FORBIDDEN],
                 projectId=pid)
      except GAPI_forbidden:
        pass

def _showSchema(schema):
  print u'Schema: %s' % schema[u'schemaName']
  for a_key in schema:
    if a_key not in [u'schemaName', u'fields', u'etag', u'kind']:
      print u' %s: %s' % (a_key, schema[a_key])
  for field in schema[u'fields']:
    print u' Field: %s' % field[u'fieldName']
    for a_key in field:
      if a_key not in [u'fieldName', u'kind', u'etag']:
        print u'  %s: %s' % (a_key, field[a_key])

SCHEMA_FIELDTYPE_CHOICES_MAP = {
  u'bool': u'BOOL',
  u'date': u'DATE',
  u'double': u'DOUBLE',
  u'email': u'EMAIL',
  u'int64': u'INT64',
  u'phone': u'PHONE',
  u'string': u'STRING',
  }

def doCreateOrUpdateUserSchema(updateCmd):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  schemaKey = getString(OB_SCHEMA_NAME)
  if updateCmd:
    try:
      body = callGAPI(cd.schemas(), u'get', throw_reasons=[GAPI_NOT_FOUND], customerId=GC_Values[GC_CUSTOMER_ID], schemaKey=schemaKey)
    except GAPI_notFound:
      sys.stderr.write(u'ERROR: Schema %s does not exist.\n' % schemaKey)
      sys.exit(3)
  else:
    body = {u'schemaName': schemaKey, u'fields': []}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'field':
      fieldName = getString(OB_FIELD_NAME)
      if updateCmd: # clear field if it exists on update
        for n, field in enumerate(body[u'fields']):
          if field[u'fieldName'].lower() == fieldName.lower():
            del body[u'fields'][n]
            break
      a_field = {u'fieldName': fieldName, u'fieldType': u'STRING'}
      while True:
        myarg = getArgument()
        if myarg == u'type':
          a_field[u'fieldType'] = getChoice(SCHEMA_FIELDTYPE_CHOICES_MAP, mapChoice=True)
        elif myarg in [u'multivalued', u'multivalue']:
          a_field[u'multiValued'] = True
        elif myarg == u'indexed':
          a_field[u'indexed'] = True
        elif myarg == u'restricted':
          a_field[u'readAccessType'] = u'ADMINS_AND_SELF'
        elif myarg == u'range':
          a_field[u'numericIndexingSpec'] = {u'minValue': getInteger(), u'maxValue': getInteger()}
        elif myarg == u'endfield':
          body[u'fields'].append(a_field)
          break
        elif myarg == u'field':
          putArgumentBack()
          break
        else:
          unknownArgumentExit()
    elif updateCmd and myarg == u'deletefield':
      fieldName = getString(OB_FIELD_NAME)
      for n, field in enumerate(body[u'fields']):
        if field[u'fieldName'].lower() == fieldName.lower():
          del body[u'fields'][n]
          break
      else:
        usageErrorExit(PHRASE_FIELD_NOT_FOUND_IN_SCHEMA.format(fieldName, schemaKey))
    else:
      unknownArgumentExit()
  if updateCmd:
    result = callGAPI(cd.schemas(), u'update', customerId=GC_Values[GC_CUSTOMER_ID], body=body, schemaKey=schemaKey)
    print u'Updated user schema %s' % result[u'schemaName']
  else:
    result = callGAPI(cd.schemas(), u'insert', customerId=GC_Values[GC_CUSTOMER_ID], body=body)
    print u'Created user schema %s' % result[u'schemaName']

def doDeleteUserSchema():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  schemaKey = getString(OB_SCHEMA_NAME)
  checkForExtraneousArguments()
  callGAPI(cd.schemas(), u'delete', customerId=GC_Values[GC_CUSTOMER_ID], schemaKey=schemaKey)
  print u'Deleted schema %s' % schemaKey

def doInfoUserSchema():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  schemaKey = getString(OB_SCHEMA_NAME)
  checkForExtraneousArguments()
  schema = callGAPI(cd.schemas(), u'get', customerId=GC_Values[GC_CUSTOMER_ID], schemaKey=schemaKey)
  _showSchema(schema)

def doPrintShowUserSchemas(csvFormat):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  if csvFormat:
    todrive = False
    csvRows = []
    titles = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if csvFormat and myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  schemas = callGAPI(cd.schemas(), u'list', customerId=GC_Values[GC_CUSTOMER_ID])
  if not schemas or u'schemas' not in schemas:
    return
  for schema in schemas[u'schemas']:
    if not csvFormat:
      _showSchema(schema)
    else:
      row = {u'fields': len(schema[u'fields'])}
      addRowTitlesToCSVfile(flattenJSON(schema, flattened=row), csvRows, titles)
  if csvFormat:
    sortCSVTitles([u'schemaId', u'schemaName', u'fields'], titles)
    writeCSVfile(csvRows, titles, u'User Schemas', todrive)

ADDRESS_TYPES = [u'custom', u'home', u'other', u'work']
EXTERNALID_TYPES = [u'account', u'customer', u'network', u'organization']
IM_PROTOCOLS = [u'custom_protocol', u'aim', u'gtalk', u'icq', u'jabber', u'msn', u'net_meeting', u'qq', u'skype', u'xmpp', u'yahoo']
IM_TYPES = [u'custom', u'home', u'other', u'work']
NOTE_TYPES = [u'text_plain', u'text_html']
ORGANIZATION_TYPES = [u'domain_only', u'school', u'unknown', u'work']
OTHEREMAIL_TYPES = [u'custom', u'home', u'other', u'work']
PHONE_TYPES = [u'assistant', u'callback', u'car', u'company_main', u'custom', u'grand_central', u'home', u'home_fax', u'isdn', u'main', u'mobile', u'other', u'other_fax', u'pager', u'radio', u'telex', u'tty_tdd', u'work', u'work_fax', u'work_mobile', u'work_pager']
RELATION_TYPES = [u'mother', u'father', u'sister', u'brother', u'manager', u'assistant', u'partner']
SCHEMA_TYPES = [u'custom', u'home', u'other', u'work']
WEBSITE_TYPES = [u'home_page', u'blog', u'profile', u'work', u'home', u'other', u'ftp', u'reservations', u'app_install_page']

UPDATE_USER_ARGUMENT_TO_PROPERTY_MAP = {
  u'address': u'addresses',
  u'addresses': u'addresses',
  u'agreed2terms': u'agreedToTerms',
  u'agreedtoterms': u'agreedToTerms',
  u'changepassword': u'changePasswordAtNextLogin',
  u'changepasswordatnextlogin': u'changePasswordAtNextLogin',
  u'crypt': u'hashFunction',
  u'customerid': u'customerId',
  u'email': u'primaryEmail',
  u'emails': u'emails',
  u'externalid': u'externalIds',
  u'externalids': u'externalIds',
  u'familyname': u'familyName',
  u'firstname': u'givenName',
  u'gal': u'includeInGlobalAddressList',
  u'givenname': u'givenName',
  u'im': u'ims',
  u'ims': u'ims',
  u'includeinglobaladdresslist': u'includeInGlobalAddressList',
  u'ipwhitelisted': u'ipWhitelisted',
  u'lastname': u'familyName',
  u'md5': u'hashFunction',
  u'name': u'name',
  u'note': u'notes',
  u'notes': u'notes',
  u'org': u'orgUnitPath',
  u'organization': u'organizations',
  u'organizations': u'organizations',
  u'orgunitpath': u'orgUnitPath',
  u'otheremail': u'emails',
  u'ou': u'orgUnitPath',
  u'password': u'password',
  u'phone': u'phones',
  u'phones': u'phones',
  u'primaryemail': u'primaryEmail',
  u'relation': u'relations',
  u'relations': u'relations',
  u'sha': u'hashFunction',
  u'sha-1': u'hashFunction',
  u'sha1': u'hashFunction',
  u'suspended': u'suspended',
  u'username': u'primaryEmail',
  u'website': u'websites',
  u'websites': u'websites',
  }

USER_BOOLEAN_PROPERTIES = [
  u'suspended',
  u'includeInGlobalAddressList',
  u'changePasswordAtNextLogin',
  u'ipWhitelisted',
  u'agreedToTerms',
  ]

HASH_FUNCTION_MAP = {
  u'sha': u'SHA-1',
  u'sha1': u'SHA-1',
  u'sha-1': u'SHA-1',
  u'md5': u'MD5',
  u'crypt': u'crypt',
}

ADDRESS_ARGUMENT_TO_FIELD_MAP = {
  u'country': u'country',
  u'countrycode': u'countryCode',
  u'extendedaddress': u'extendedAddress',
  u'locality': u'locality',
  u'pobox': u'poBox',
  u'postalcode': u'postalCode',
  u'region': u'region',
  u'streetaddress': u'streetAddress',
  }

ORGANIZATION_ARGUMENT_TO_FIELD_MAP = {
  u'costcenter': u'costCenter',
  u'department': u'department',
  u'description': u'description',
  u'domain': u'domain',
  u'location': u'location',
  u'name': u'name',
  u'symbol': u'symbol',
  u'title': u'title',
  }

def getUserAttributes(cd, updateCmd=False, noUid=False):
  def clearBodyList(body, itemName):
    if itemName in body:
      del body[itemName]
    body.setdefault(itemName, None)

  def appendItemToBodyList(body, itemName, itemValue, checkBlankField=None):
    if (itemName in body) and (body[itemName] is None):
      del body[itemName]
    body.setdefault(itemName, [])
    if checkBlankField is None or itemValue[checkBlankField]:
      body[itemName].append(itemValue)

  def gen_sha512_hash(password):
    from passlib.handlers.sha2_crypt import sha512_crypt
    return sha512_crypt.encrypt(password, rounds=5000)

  def _splitSchemaNameDotFieldName(sn_fn, fnRequired=True):
    if sn_fn.find(u'.') != -1:
      schemaName, fieldName = sn_fn.split(u'.', 1)
      schemaName = schemaName.strip()
      fieldName = fieldName.strip()
      if schemaName and fieldName:
        return (schemaName, fieldName)
    elif not fnRequired:
      schemaName = sn_fn.strip()
      if schemaName:
        return (schemaName, None)
    invalidArgumentExit(OB_SCHEMA_NAME_FIELD_NAME)

  if updateCmd:
    body = {}
    need_password = False
  else:
    body = {u'name': {u'givenName': u'Unknown', u'familyName': u'Unknown'}}
    body[u'primaryEmail'] = getEmailAddress(noUid=noUid)
    need_password = True
  need_to_hash_password = True
  admin_body = {}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'admin':
      admin_body[u'status'] = getBoolean()
    elif myarg == u'nohash':
      need_to_hash_password = False
    elif myarg in UPDATE_USER_ARGUMENT_TO_PROPERTY_MAP:
      up = UPDATE_USER_ARGUMENT_TO_PROPERTY_MAP[myarg]
      if up == u'givenName':
        body.setdefault(u'name', {})
        body[u'name'][up] = getString(OB_STRING, minLen=0)
      elif up == u'familyName':
        body.setdefault(u'name', {})
        body[u'name'][up] = getString(OB_STRING, minLen=0)
      elif up == u'password':
        need_password = False
        body[up] = getString(OB_STRING)
        if body[up].lower() == u'random':
          need_password = True
      elif up in USER_BOOLEAN_PROPERTIES:
        body[up] = getBoolean()
      elif up == u'hashFunction':
        body[up] = HASH_FUNCTION_MAP[myarg]
        need_to_hash_password = False
      elif up == u'primaryEmail' and updateCmd:
        body[up] = getEmailAddress(noUid=True)
      elif up == u'customerId' and updateCmd:
        body[up] = getString(OB_STRING)
      elif up == u'orgUnitPath':
        body[up] = getOrgUnitPath()
      elif up == u'addresses':
        if checkArgumentPresent(CLEAR_NONE_ARGUMENT):
          clearBodyList(body, up)
          continue
        entry = {}
        getChoice([u'type',])
        entry[u'type'] = getChoice(ADDRESS_TYPES)
        if entry[u'type'] == u'custom':
          entry[u'customType'] = getString(OB_STRING)
        if checkArgumentPresent(UNSTRUCTURED_FORMATTED_ARGUMENT):
          entry[u'sourceIsStructured'] = False
          entry[u'formatted'] = getString(OB_STRING, minLen=0).replace(u'\\n', u'\n')
        while CL_argvI < CL_argvLen:
          argument = getArgument()
          if argument in ADDRESS_ARGUMENT_TO_FIELD_MAP:
            value = getString(OB_STRING, minLen=0)
            if value:
              entry[ADDRESS_ARGUMENT_TO_FIELD_MAP[argument]] = value
          elif argument == u'notprimary':
            break
          elif argument == u'primary':
            entry[u'primary'] = True
            break
          else:
            unknownArgumentExit()
        appendItemToBodyList(body, up, entry)
      elif up == u'ims':
        if checkArgumentPresent(CLEAR_NONE_ARGUMENT):
          clearBodyList(body, up)
          continue
        entry = {}
        getChoice([u'type',])
        entry[u'type'] = getChoice(IM_TYPES)
        if entry[u'type'] == u'custom':
          entry[u'customType'] = getString(OB_STRING)
        getChoice([u'protocol',])
        entry[u'protocol'] = getChoice(IM_PROTOCOLS)
        if entry[u'protocol'] == u'custom_protocol':
          entry[u'customProtocol'] = getString(OB_STRING)
        # Backwards compatability: notprimary|primary on either side of IM address
        entry[u'primary'] = getChoice(PRIMARY_NOTPRIMARY_CHOICE_MAP, defaultChoice=False, mapChoice=True)
        entry[u'im'] = getString(OB_STRING, minLen=0)
        entry[u'primary'] = getChoice(PRIMARY_NOTPRIMARY_CHOICE_MAP, defaultChoice=entry[u'primary'], mapChoice=True)
        appendItemToBodyList(body, up, entry, u'im')
      elif up == u'notes':
        if checkArgumentPresent(CLEAR_NONE_ARGUMENT):
          clearBodyList(body, up)
          continue
        entry = {}
        entry[u'contentType'] = getChoice(NOTE_TYPES, defaultChoice=u'text_plain')
        if checkArgumentPresent(FILE_ARGUMENT):
          entry[u'value'] = readFile(getString(OB_FILE_NAME), encoding=GM_Globals[GM_SYS_ENCODING])
        else:
          entry[u'value'] = getString(OB_STRING, minLen=0).replace(u'\\n', u'\n')
        body[up] = entry
      elif up == u'organizations':
        if checkArgumentPresent(CLEAR_NONE_ARGUMENT):
          clearBodyList(body, up)
          continue
        entry = {}
        while CL_argvI < CL_argvLen:
          argument = getArgument()
          if argument == u'type':
            entry[u'type'] = getChoice(ORGANIZATION_TYPES)
          elif argument == u'customtype':
            entry[u'customType'] = getString(OB_STRING)
          elif argument in ORGANIZATION_ARGUMENT_TO_FIELD_MAP:
            value = getString(OB_STRING, minLen=0)
            if value:
              entry[ORGANIZATION_ARGUMENT_TO_FIELD_MAP[argument]] = value
          elif argument == u'notprimary':
            break
          elif argument == u'primary':
            entry[u'primary'] = True
            break
          else:
            unknownArgumentExit()
        appendItemToBodyList(body, up, entry)
      elif up == u'phones':
        if checkArgumentPresent(CLEAR_NONE_ARGUMENT):
          clearBodyList(body, up)
          continue
        entry = {}
        while CL_argvI < CL_argvLen:
          argument = getArgument()
          if argument == u'type':
            entry[u'type'] = getChoice(PHONE_TYPES)
            if entry[u'type'] == u'custom':
              entry[u'customType'] = getString(OB_STRING)
          elif argument == u'value':
            entry[u'value'] = getString(OB_STRING, minLen=0)
          elif argument == u'notprimary':
            break
          elif argument == u'primary':
            entry[u'primary'] = True
            break
          else:
            unknownArgumentExit()
        appendItemToBodyList(body, up, entry, u'value')
      elif up == u'relations':
        if checkArgumentPresent(CLEAR_NONE_ARGUMENT):
          clearBodyList(body, up)
          continue
        entry = {}
        entry[u'type'] = getString(OB_STRING)
        if entry[u'type'].lower() not in RELATION_TYPES:
          entry[u'customType'] = entry[u'type']
          entry[u'type'] = u'custom'
        else:
          entry[u'type'] = entry[u'type'].lower()
        entry[u'value'] = getString(OB_STRING, minLen=0)
        appendItemToBodyList(body, up, entry, u'value')
      elif up == u'emails':
        if checkArgumentPresent(CLEAR_NONE_ARGUMENT):
          clearBodyList(body, up)
          continue
        entry = {}
        entry[u'type'] = getString(OB_STRING)
        if entry[u'type'].lower() not in OTHEREMAIL_TYPES:
          entry[u'customType'] = entry[u'type']
          entry[u'type'] = u'custom'
        else:
          entry[u'type'] = entry[u'type'].lower()
        entry[u'address'] = getEmailAddress(noUid=True, minLen=0)
        appendItemToBodyList(body, up, entry, u'address')
      elif up == u'externalIds':
        if checkArgumentPresent(CLEAR_NONE_ARGUMENT):
          clearBodyList(body, up)
          continue
        entry = {}
        entry[u'type'] = getString(OB_STRING)
        if entry[u'type'].lower() not in EXTERNALID_TYPES:
          entry[u'customType'] = entry[u'type']
          entry[u'type'] = u'custom'
        else:
          entry[u'type'] = entry[u'type'].lower()
        entry[u'value'] = getString(OB_STRING, minLen=0)
        appendItemToBodyList(body, up, entry, u'value')
      elif up == u'websites':
        if checkArgumentPresent(CLEAR_NONE_ARGUMENT):
          clearBodyList(body, up)
          continue
        entry = {}
        entry[u'type'] = getString(OB_STRING)
        if entry[u'type'].lower() not in WEBSITE_TYPES:
          entry[u'customType'] = entry[u'type']
          entry[u'type'] = u'custom'
        else:
          entry[u'type'] = entry[u'type'].lower()
        entry[u'value'] = getString(OB_URL, minLen=0)
        entry[u'primary'] = getChoice(PRIMARY_NOTPRIMARY_CHOICE_MAP, defaultChoice=False, mapChoice=True)
        appendItemToBodyList(body, up, entry, u'value')
    elif myarg == u'clearschema':
      if not updateCmd:
        unknownArgumentExit()
      schemaName, fieldName = _splitSchemaNameDotFieldName(getString(OB_SCHEMA_NAME_FIELD_NAME), False)
      up = u'customSchemas'
      body.setdefault(up, {})
      body[up].setdefault(schemaName, {})
      if fieldName is None:
        try:
          schema = callGAPI(cd.schemas(), u'get',
                            throw_reasons=[GAPI_INVALID, GAPI_BAD_REQUEST, GAPI_RESOURCE_NOT_FOUND, GAPI_FORBIDDEN],
                            customerId=GC_Values[GC_CUSTOMER_ID], schemaKey=schemaName, fields=u'fields(fieldName)')
          for field in schema[u'fields']:
            body[up][schemaName][field[u'fieldName']] = None
        except (GAPI_invalid, GAPI_badRequest, GAPI_resourceNotFound, GAPI_forbidden):
          entityDoesNotExistWarning(u'Schema', schemaName, 0, 0)
          unknownArgumentExit()
      else:
        body[up][schemaName][fieldName] = None
    elif myarg.find(u'.') >= 0:
      schemaName, fieldName = _splitSchemaNameDotFieldName(CL_argv[CL_argvI-1])
      up = u'customSchemas'
      body.setdefault(up, {})
      body[up].setdefault(schemaName, {})
      if checkArgumentPresent(MULTIVALUE_ARGUMENT):
        body[up][schemaName].setdefault(fieldName, [])
        schemaValue = {}
        if checkArgumentPresent([u'type',]):
          schemaValue[u'type'] = getChoice(SCHEMA_TYPES)
          if schemaValue[u'type'] == u'custom':
            schemaValue[u'customType'] = getString(OB_STRING)
        schemaValue[u'value'] = getString(OB_STRING)
        body[up][schemaName][fieldName].append(schemaValue)
      else:
        body[up][schemaName][fieldName] = getString(OB_STRING)
    else:
      unknownArgumentExit()
  if need_password:
    body[u'password'] = u''.join(random.sample(u'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789~`!@#$%^&*()-=_+:;"\'{}[]\\|', 25))
  if u'password' in body and need_to_hash_password:
    body[u'password'] = gen_sha512_hash(body[u'password'])
    body[u'hashFunction'] = u'crypt'
  return (body, admin_body)

def doCreateUser():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  body, admin_body = getUserAttributes(cd, updateCmd=False, noUid=True)
  print u"Creating account for %s" % body[u'primaryEmail']
  callGAPI(cd.users(), u'insert', body=body, fields=u'primaryEmail')
  if admin_body:
    print u' Changing admin status for %s to %s' % (body[u'primaryEmail'], admin_body[u'status'])
    callGAPI(cd.users(), u'makeAdmin', userKey=body[u'primaryEmail'], body=admin_body)

def doUpdateUser(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  body, admin_body = getUserAttributes(cd, updateCmd=True)
  for user in users:
    user = normalizeEmailAddressOrUID(user)
    if u'primaryEmail' in body and body[u'primaryEmail'][:4].lower() == u'vfe@':
      user_primary = callGAPI(cd.users(), u'get', userKey=user, fields=u'primaryEmail,id')
      user = user_primary[u'id']
      user_primary = user_primary[u'primaryEmail']
      user_name, user_domain = splitEmailAddress(user_primary)
      body[u'primaryEmail'] = u'vfe.%s.%05d@%s' % (user_name, random.randint(1, 99999), user_domain)
      body[u'emails'] = [{u'type': u'custom', u'customType': u'former_employee', u'primary': False, u'address': user_primary}]
    sys.stdout.write(u'updating user %s...\n' % (user))
    if body:
      callGAPI(cd.users(), u'patch', userKey=user, body=body)
    if admin_body:
      callGAPI(cd.users(), u'makeAdmin', userKey=user, body=admin_body)

def doDeleteUser():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  user_email = getEmailAddress()
  checkForExtraneousArguments()
  print u"Deleting account for %s" % (user_email)
  callGAPI(cd.users(), u'delete', userKey=user_email)

def doUndeleteUser():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  user = getEmailAddress()
  if checkArgumentPresent(ORG_OU_ARGUMENT):
    orgUnit = getOrgUnitPath()
  else:
    orgUnit = u'/'
  checkForExtraneousArguments()
  user_uid = user if user.find(u'@') == -1 else None
  if not user_uid:
    print u'Looking up UID for %s...' % user
    deleted_users = callGAPIpages(cd.users(), u'list', u'users',
                                  customer=GC_Values[GC_CUSTOMER_ID], showDeleted=True, maxResults=GC_Values[GC_USER_MAX_RESULTS])
    matching_users = []
    for deleted_user in deleted_users:
      if str(deleted_user[u'primaryEmail']).lower() == user:
        matching_users.append(deleted_user)
    if len(matching_users) < 1:
      sys.stderr.write(u'ERROR: could not find deleted user with that address.\n')
      sys.exit(3)
    elif len(matching_users) > 1:
      print u'ERROR: more than one matching deleted %s user. Please select the correct one to undelete and specify with "gam undelete user uid:<uid>"' % user
      print u''
      for matching_user in matching_users:
        print u' uid:%s ' % matching_user[u'id']
        for attr_name in [u'creationTime', u'lastLoginTime', u'deletionTime']:
          try:
            if matching_user[attr_name] == NEVER_TIME:
              matching_user[attr_name] = u'Never'
            print u'   %s: %s ' % (attr_name, matching_user[attr_name])
          except KeyError:
            pass
        print
      setSysExitRC(3)
      return
    else:
      user_uid = matching_users[0][u'id']
  print u"Undeleting account for %s" % user
  callGAPI(cd.users(), u'undelete', userKey=user_uid, body={u'orgUnitPath': orgUnit})

INFO_USER_OPTIONS = [u'noaliases', u'nogroups', u'nolicenses', u'nolicences', u'noschemas', u'schemas', u'userview',]

def doInfoUser(user_email=None):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  if user_email is None:
    if CL_argvI < CL_argvLen:
      user_email = getEmailAddress(optional=True, minLen=0)
    else:
      storage = oauth2client.file.Storage(GC_Values[GC_OAUTH2_TXT])
      credentials = storage.get()
      if credentials is None or credentials.invalid:
        doOAuthRequest()
        credentials = storage.get()
      user_email = credentials.id_token[u'email']
  getSchemas = getAliases = getGroups = getLicenses = True
  projection = u'full'
  fieldsList = []
  customFieldMask = viewType = None
  skus = [u'Google-Apps-For-Business', u'Google-Apps-Unlimited', u'Google-Apps-For-Postini',
          u'Google-Apps-Lite', u'Google-Vault', u'Google-Vault-Former-Employee']
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'noaliases':
      getAliases = False
    elif myarg == u'nogroups':
      getGroups = False
    elif myarg in [u'nolicenses', u'nolicences']:
      getLicenses = False
    elif myarg in [u'products', u'product']:
      skus = []
      for productId in getGoogleProductListMap():
        skus += [skuId for skuId in GOOGLE_SKUS if GOOGLE_SKUS[skuId] == productId]
    elif myarg in [u'sku', u'skus']:
      skus = getGoogleSKUListMap()
    elif myarg == u'noschemas':
      getSchemas = False
      projection = u'basic'
    elif myarg in [u'custom', u'schemas']:
      getSchemas = True
      projection = u'custom'
      customFieldMask = getString(OB_SCHEMA_NAME_LIST)
    elif myarg == u'userview':
      viewType = u'domain_public'
      getGroups = getLicenses = False
    elif myarg in USER_ARGUMENT_TO_PROPERTY_MAP:
      if not fieldsList:
        fieldsList = [u'primaryEmail',]
      fieldsList.extend(USER_ARGUMENT_TO_PROPERTY_MAP[myarg])
    elif myarg == u'fields':
      if not fieldsList:
        fieldsList = [u'primaryEmail',]
      fieldNameList = getString(OB_FIELD_NAME_LIST)
      for field in fieldNameList.lower().replace(u',', u' ').split():
        if field in USER_ARGUMENT_TO_PROPERTY_MAP:
          fieldsList.extend(USER_ARGUMENT_TO_PROPERTY_MAP[field])
        else:
          putArgumentBack()
          invalidChoiceExit(USER_ARGUMENT_TO_PROPERTY_MAP)
    elif myarg in INFO_GROUP_OPTIONS:
      pass
    else:
      unknownArgumentExit()
  if fieldsList:
    fields = u','.join(set(fieldsList)).replace(u'.', u'/')
  else:
    fields = None
  user = callGAPI(cd.users(), u'get',
                  userKey=user_email, projection=projection, customFieldMask=customFieldMask, viewType=viewType, fields=fields)
  print u'User: %s' % user[u'primaryEmail']
  if u'name' in user and u'givenName' in user[u'name']:
    print convertUTF8(u'First Name: %s' % user[u'name'][u'givenName'])
  if u'name' in user and u'familyName' in user[u'name']:
    print convertUTF8(u'Last Name: %s' % user[u'name'][u'familyName'])
  if u'isAdmin' in user:
    print u'Is a Super Admin: %s' % user[u'isAdmin']
  if u'isDelegatedAdmin' in user:
    print u'Is Delegated Admin: %s' % user[u'isDelegatedAdmin']
  if u'agreedToTerms' in user:
    print u'Has Agreed to Terms: %s' % user[u'agreedToTerms']
  if u'ipWhitelisted' in user:
    print u'IP Whitelisted: %s' % user[u'ipWhitelisted']
  if u'suspended' in user:
    print u'Account Suspended: %s' % user[u'suspended']
  if u'suspensionReason' in user:
    print u'Suspension Reason: %s' % user[u'suspensionReason']
  if u'changePasswordAtNextLogin' in user:
    print u'Must Change Password: %s' % user[u'changePasswordAtNextLogin']
  if u'id' in user:
    print u'Google Unique ID: %s' % user[u'id']
  if u'customerId' in user:
    print u'Customer ID: %s' % user[u'customerId']
  if u'isMailboxSetup' in user:
    print u'Mailbox is setup: %s' % user[u'isMailboxSetup']
  if u'includeInGlobalAddressList' in user:
    print u'Included in GAL: %s' % user[u'includeInGlobalAddressList']
  if u'creationTime' in user:
    print u'Creation Time: %s' % user[u'creationTime']
  if u'lastLoginTime' in user:
    if user[u'lastLoginTime'] == NEVER_TIME:
      print u'Last login time: Never'
    else:
      print u'Last login time: %s' % user[u'lastLoginTime']
  if u'orgUnitPath' in user:
    print u'Google Org Unit Path: %s\n' % user[u'orgUnitPath']
  if u'thumbnailPhotoUrl' in user:
    print u'Photo URL: %s\n' % user[u'thumbnailPhotoUrl']
  if u'notes' in user:
    print u'Notes:'
    notes = user[u'notes']
    if isinstance(notes, dict):
      contentType = notes.get(u'contentType', u'text_plain')
      print u' %s: %s' % (u'contentType', contentType)
      if contentType == u'text_html':
        print convertUTF8(indentMultiLineText(u' value: {0}'.format(dehtml(notes[u'value'])), n=2))
      else:
        print convertUTF8(indentMultiLineText(u' value: {0}'.format(notes[u'value']), n=2))
    else:
      print convertUTF8(indentMultiLineText(u' value: {0}'.format(notes), n=2))
    print u''
  if u'ims' in user:
    print u'IMs:'
    for im in user[u'ims']:
      for key in im:
        print convertUTF8(u' %s: %s' % (key, im[key]))
      print u''
  if u'addresses' in user:
    print u'Addresses:'
    for address in user[u'addresses']:
      for key in address:
        if key != u'formatted':
          print convertUTF8(u' %s: %s' % (key, address[key]))
        else:
          print convertUTF8(u' %s: %s' % (key, address[key].replace(u'\n', u'\\n')))
      print u''
  if u'organizations' in user:
    print u'Organizations:'
    for org in user[u'organizations']:
      for key in org:
        if key == u'customType' and not org[key]:
          continue
        print convertUTF8(u' %s: %s' % (key, org[key]))
      print u''
  if u'phones' in user:
    print u'Phones:'
    for phone in user[u'phones']:
      for key in phone:
        print convertUTF8(u' %s: %s' % (key, phone[key]))
      print u''
  if u'emails' in user:
    if len(user[u'emails']) > 1:
      print u'Other Emails:'
      for an_email in user[u'emails']:
        if an_email[u'address'].lower() == user[u'primaryEmail'].lower():
          continue
        for key in an_email:
          if key == u'type' and an_email[key] == u'custom':
            continue
          if key == u'customType':
            print convertUTF8(u' type: %s' % an_email[key])
          else:
            print convertUTF8(u' %s: %s' % (key, an_email[key]))
      print u''
  if u'relations' in user:
    print u'Relations:'
    for relation in user[u'relations']:
      for key in relation:
        if key == u'type' and relation[key] == u'custom':
          continue
        elif key == u'customType':
          print convertUTF8(u' %s: %s' % (u'type', relation[key]))
        else:
          print convertUTF8(u' %s: %s' % (key, relation[key]))
      print u''
  if u'externalIds' in user:
    print u'External IDs:'
    for externalId in user[u'externalIds']:
      for key in externalId:
        if key == u'type' and externalId[key] == u'custom':
          continue
        elif key == u'customType':
          print convertUTF8(u' %s: %s' % (u'type', externalId[key]))
        else:
          print convertUTF8(u' %s: %s' % (key, externalId[key]))
      print u''
  if u'websites' in user:
    print u'Websites:'
    for website in user[u'websites']:
      for key in website:
        if key == u'type' and website[key] == u'custom':
          continue
        elif key == u'customType':
          print convertUTF8(u' %s: %s' % (u'type', website[key]))
        else:
          print convertUTF8(u' %s: %s' % (key, website[key]))
      print u''
  if getSchemas:
    if u'customSchemas' in user:
      print u'Custom Schemas:'
      for schema in user[u'customSchemas']:
        print u' Schema: %s' % schema
        for field in user[u'customSchemas'][schema]:
          if isinstance(user[u'customSchemas'][schema][field], list):
            print u'  %s:' % field
            for an_item in user[u'customSchemas'][schema][field]:
              print convertUTF8(u'   type: %s' % (an_item[u'type']))
              if an_item[u'type'] == u'custom':
                print convertUTF8(u'    customType: %s' % (an_item[u'customType']))
              print convertUTF8(u'    value: %s' % (an_item[u'value']))
          else:
            print convertUTF8(u'  %s: %s' % (field, user[u'customSchemas'][schema][field]))
        print
  if getAliases:
    if u'aliases' in user:
      print u'Email Aliases:'
      for alias in user[u'aliases']:
        print u'  %s' % alias
    if u'nonEditableAliases' in user:
      print u'Non-Editable Aliases:'
      for alias in user[u'nonEditableAliases']:
        print u'  %s' % alias
  if getGroups:
    groups = callGAPIpages(cd.groups(), u'list', u'groups', userKey=user_email, fields=u'groups(name,email),nextPageToken')
    if len(groups) > 0:
      print u'Groups: (%s)' % len(groups)
      for group in groups:
        print u'   %s <%s>' % (group[u'name'], group[u'email'])
  if getLicenses:
    print u'Licenses:'
    lic = buildGAPIObject(GAPI_LICENSING_API)
    for skuId in skus:
      try:
        result = callGAPI(lic.licenseAssignments(), u'get',
                          throw_reasons=[GAPI_USER_NOT_FOUND, GAPI_FORBIDDEN, GAPI_NOT_FOUND],
                          userId=user_email, productId=GOOGLE_SKUS[skuId], skuId=skuId)
        print u' %s' % result[u'skuId']
      except GAPI_notFound:
        continue
      except (GAPI_userNotFound, GAPI_forbidden):
        break

USER_ARGUMENT_TO_PROPERTY_MAP = {
  u'address': [u'addresses',],
  u'addresses': [u'addresses',],
  u'admin': [u'isAdmin', u'isDelegatedAdmin',],
  u'agreed2terms': [u'agreedToTerms',],
  u'agreedtoterms': [u'agreedToTerms',],
  u'aliases': [u'aliases', u'nonEditableAliases',],
  u'changepassword': [u'changePasswordAtNextLogin',],
  u'changepasswordatnextlogin': [u'changePasswordAtNextLogin',],
  u'creationtime': [u'creationTime',],
  u'deletiontime': [u'deletionTime',],
  u'email': [u'emails',],
  u'emails': [u'emails',],
  u'externalid': [u'externalIds',],
  u'externalids': [u'externalIds',],
  u'familyname': [u'name.familyName',],
  u'firstname': [u'name.givenName',],
  u'fullname': [u'name.fullName',],
  u'gal': [u'includeInGlobalAddressList',],
  u'givenname': [u'name.givenName',],
  u'id': [u'id',],
  u'im': [u'ims',],
  u'ims': [u'ims',],
  u'includeinglobaladdresslist': [u'includeInGlobalAddressList',],
  u'ipwhitelisted': [u'ipWhitelisted',],
  u'isadmin': [u'isAdmin', u'isDelegatedAdmin',],
  u'isdelegatedadmin': [u'isAdmin', u'isDelegatedAdmin',],
  u'ismailboxsetup': [u'isMailboxSetup',],
  u'lastlogintime': [u'lastLoginTime',],
  u'lastname': [u'name.familyName',],
  u'name': [u'name.givenName', u'name.familyName', u'name.fullName',],
  u'nicknames': [u'aliases', u'nonEditableAliases',],
  u'noneditablealiases': [u'aliases', u'nonEditableAliases',],
  u'note': [u'notes',],
  u'notes': [u'notes',],
  u'org': [u'orgUnitPath',],
  u'organization': [u'organizations',],
  u'organizations': [u'organizations',],
  u'orgunitpath': [u'orgUnitPath',],
  u'otheremail': [u'emails',],
  u'otheremails': [u'emails',],
  u'ou': [u'orgUnitPath',],
  u'phone': [u'phones',],
  u'phones': [u'phones',],
  u'photo': [u'thumbnailPhotoUrl',],
  u'photourl': [u'thumbnailPhotoUrl',],
  u'primaryemail': [u'primaryEmail',],
  u'relation': [u'relations',],
  u'relations': [u'relations',],
  u'suspended': [u'suspended', u'suspensionReason',],
  u'thumbnailphotourl': [u'thumbnailPhotoUrl',],
  u'username': [u'primaryEmail',],
  u'website': [u'websites',],
  u'websites': [u'websites',],
  }

USERS_ORDERBY_CHOICES_MAP = {
  u'familyname': u'familyName',
  u'lastname': u'familyName',
  u'givenname': u'givenName',
  u'firstname': u'givenName',
  u'email': u'email',
  }

def doPrintUsers():
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  todrive = False
  fieldsList = []
  fieldsTitles = {}
  titles = []
  csvRows = []
  addFieldToCSVfile(u'primaryemail', USER_ARGUMENT_TO_PROPERTY_MAP, fieldsList, fieldsTitles, titles)
  customer = GC_Values[GC_CUSTOMER_ID]
  domain = None
  query = None
  projection = u'basic'
  customFieldMask = None
  sortHeaders = getGroupFeed = getLicenseFeed = email_parts = False
  viewType = deleted_only = orderBy = sortOrder = None
  delimiter = GC_Values[GC_CSV_OUTPUT_FIELD_DELIMITER]
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'todrive':
      todrive = True
    elif myarg == u'domain':
      domain = getString(OB_DOMAIN_NAME).lower()
      customer = None
    elif myarg == u'query':
      query = getString(OB_QUERY)
    elif myarg in [u'deletedonly', u'onlydeleted']:
      deleted_only = True
    elif myarg == u'orderby':
      orderBy = getChoice(USERS_ORDERBY_CHOICES_MAP, mapChoice=True)
    elif myarg in SORTORDER_CHOICES_MAP:
      sortOrder = SORTORDER_CHOICES_MAP[myarg]
    elif myarg == u'userview':
      viewType = u'domain_public'
    elif myarg in [u'custom', u'schemas']:
      fieldsList.append(u'customSchemas')
      customFieldMask = getString(OB_SCHEMA_NAME_LIST).replace(u' ', u',')
      if customFieldMask.lower() == u'all':
        customFieldMask = None
        projection = u'full'
      else:
        projection = u'custom'
    elif myarg == u'delimiter':
      delimiter = getString(OB_STRING, minLen=1, maxLen=1)
    elif myarg in PROJECTION_CHOICES_MAP:
      projection = myarg
      sortHeaders = True
      fieldsList = []
    elif myarg == u'allfields':
      projection = u'basic'
      sortHeaders = True
      fieldsList = []
    elif myarg in USER_ARGUMENT_TO_PROPERTY_MAP:
      if not fieldsList:
        fieldsList = [u'primaryEmail',]
      addFieldToCSVfile(myarg, USER_ARGUMENT_TO_PROPERTY_MAP, fieldsList, fieldsTitles, titles)
    elif myarg == u'fields':
      if not fieldsList:
        fieldsList = [u'primaryEmail',]
      fieldNameList = getString(OB_FIELD_NAME_LIST)
      for field in fieldNameList.lower().replace(u',', u' ').split():
        if field in USER_ARGUMENT_TO_PROPERTY_MAP:
          addFieldToCSVfile(field, USER_ARGUMENT_TO_PROPERTY_MAP, fieldsList, fieldsTitles, titles)
        else:
          putArgumentBack()
          invalidChoiceExit(USER_ARGUMENT_TO_PROPERTY_MAP)
    elif myarg == u'groups':
      getGroupFeed = True
    elif myarg in [u'license', u'licenses', u'licence', u'licences']:
      getLicenseFeed = True
    elif myarg in [u'emailpart', u'emailparts', u'username']:
      email_parts = True
    else:
      unknownArgumentExit()
  if fieldsList:
    fields = u'nextPageToken,users(%s)' % u','.join(set(fieldsList)).replace(u'.', u'/')
  else:
    fields = None
  sys.stderr.write(u"Getting all users in G Suite account (may take some time on a large account)...\n")
  page_message = u'Got %%total_items%% users: %%first_item%% - %%last_item%%\n'
  feed = callGAPIpages(cd.users(), u'list', u'users', page_message=page_message,
                       message_attribute=u'primaryEmail', customer=customer, domain=domain, fields=fields,
                       showDeleted=deleted_only, orderBy=orderBy, sortOrder=sortOrder, viewType=viewType,
                       query=query, projection=projection, customFieldMask=customFieldMask, maxResults=GC_Values[GC_USER_MAX_RESULTS])
  while feed:
    user = feed.popleft()
    if email_parts and (u'primaryEmail' in user):
      userEmail = user[u'primaryEmail']
      if userEmail.find(u'@') != -1:
        user[u'primaryEmailLocal'], user[u'primaryEmailDomain'] = splitEmailAddress(userEmail)
    addRowTitlesToCSVfile(flattenJSON(user), csvRows, titles)
  if sortHeaders:
    sortCSVTitles([u'primaryEmail',], titles)
  if getGroupFeed:
    titles.append(u'Groups')
    i = 0
    count = len(csvRows)
    for user in csvRows:
      i += 1
      userEmail = user[u'primaryEmail']
      sys.stderr.write(u"Getting Group Membership for %s%s" % (userEmail, currentCountNL(i, count)))
      groups = callGAPIpages(cd.groups(), u'list', u'groups', userKey=userEmail)
      user[u'Groups'] = delimiter.join([groupname[u'email'] for groupname in groups])
  if getLicenseFeed:
    titles.append(u'Licenses')
    licenses = doPrintLicenses(return_list=True)
    if len(licenses) > 1:
      for user in csvRows:
        user_licenses = []
        for u_license in licenses:
          if u_license[u'userId'].lower() == user[u'primaryEmail'].lower():
            user_licenses.append(u_license[u'skuId'])
        user[u'Licenses'] = delimiter.join(user_licenses)
  writeCSVfile(csvRows, titles, u'Users', todrive)

SITEVERIFICATION_SITE_TYPE_INET_DOMAIN = u'INET_DOMAIN'
SITEVERIFICATION_SITE_TYPE_SITE = u'SITE'

SITEVERIFICATION_VERIFICATION_METHOD_DNS_CNAME = u'DNS_CNAME'
SITEVERIFICATION_VERIFICATION_METHOD_DNS_TXT = u'DNS_TXT'
SITEVERIFICATION_VERIFICATION_METHOD_FILE = u'FILE'
SITEVERIFICATION_VERIFICATION_METHOD_META = u'META'

SITEVERIFICATION_METHOD_CHOICES_MAP = {
  u'cname': SITEVERIFICATION_VERIFICATION_METHOD_DNS_CNAME,
  u'txt': SITEVERIFICATION_VERIFICATION_METHOD_DNS_TXT,
  u'text': SITEVERIFICATION_VERIFICATION_METHOD_DNS_TXT,
  u'file': SITEVERIFICATION_VERIFICATION_METHOD_FILE,
  u'site': SITEVERIFICATION_VERIFICATION_METHOD_FILE,
  }

def doCreateSiteVerification():
  verif = buildGAPIObject(GAPI_SITEVERIFICATION_API)
  a_domain = getString(OB_DOMAIN_NAME)
  checkForExtraneousArguments()
  txt_record = callGAPI(verif.webResource(), u'getToken', body={u'site':{u'type':u'INET_DOMAIN', u'identifier':a_domain}, u'verificationMethod':u'DNS_TXT'})
  print u'TXT Record Name:   %s' % a_domain
  print u'TXT Record Value:  %s' % txt_record[u'token']
  print
  cname_record = callGAPI(verif.webResource(), u'getToken', body={u'site':{u'type':u'INET_DOMAIN', u'identifier':a_domain}, u'verificationMethod':u'DNS_CNAME'})
  cname_token = cname_record[u'token']
  cname_list = cname_token.split(u' ')
  cname_subdomain = cname_list[0]
  cname_value = cname_list[1]
  print u'CNAME Record Name:   %s.%s' % (cname_subdomain, a_domain)
  print u'CNAME Record Value:  %s' % cname_value
  print u''
  webserver_file_record = callGAPI(verif.webResource(), u'getToken', body={u'site':{u'type':u'SITE', u'identifier':u'http://%s/' % a_domain}, u'verificationMethod':u'FILE'})
  webserver_file_token = webserver_file_record[u'token']
  print u'Saving web server verification file to: %s' % webserver_file_token
  writeFile(webserver_file_token, u'google-site-verification: {0}'.format(webserver_file_token), continueOnError=True)
  print u'Verification File URL: http://%s/%s' % (a_domain, webserver_file_token)
  print
  webserver_meta_record = callGAPI(verif.webResource(), u'getToken', body={u'site':{u'type':u'SITE', u'identifier':u'http://%s/' % a_domain}, u'verificationMethod':u'META'})
  print u'Meta URL:               http://%s/' % a_domain
  print u'Meta HTML Header Data:  %s' % webserver_meta_record[u'token']
  print

def updateSiteVerification():
  verif = buildGAPIObject(GAPI_SITEVERIFICATION_API)
  a_domain = getString(OB_DOMAIN_NAME)
  verificationMethod = getChoice(SITEVERIFICATION_METHOD_CHOICES_MAP, mapChoice=True)
  if verificationMethod in [SITEVERIFICATION_VERIFICATION_METHOD_DNS_TXT, SITEVERIFICATION_VERIFICATION_METHOD_DNS_CNAME]:
    verify_type = SITEVERIFICATION_SITE_TYPE_INET_DOMAIN
    identifier = a_domain
  else:
    verify_type = SITEVERIFICATION_SITE_TYPE_SITE
    identifier = u'http://{0}/'.format(a_domain)
  checkForExtraneousArguments()
  body = {u'site':{u'type':verify_type, u'identifier':identifier}, u'verificationMethod':verificationMethod}
  try:
    verify_result = callGAPI(verif.webResource(), u'insert', throw_reasons=[GAPI_BAD_REQUEST], verificationMethod=verificationMethod, body=body)
  except GAPI_badRequest as e:
    error = json.loads(e.content)
    message = error[u'error'][u'errors'][0][u'message']
    print u'ERROR: %s' % message
    verify_data = callGAPI(verif.webResource(), u'getToken', body=body)
    print u'Method:  %s' % verify_data[u'method']
    print u'Token:      %s' % verify_data[u'token']
    if verify_data[u'method'] == u'DNS_CNAME':
      try:
        import dns.resolver
        resolver = dns.resolver.Resolver()
        resolver.nameservers = [u'8.8.8.8', u'8.8.4.4']
        cname_token = verify_data[u'token']
        cname_list = cname_token.split(u' ')
        cname_subdomain = cname_list[0]
        try:
          answers = resolver.query(u'%s.%s' % (cname_subdomain, a_domain), u'A')
          for answer in answers:
            print u'DNS Record: %s' % answer
        except (dns.resolver.NXDOMAIN, dns.resolver.NoAnswer):
          print u'ERROR: No such domain found in DNS!'
      except ImportError:
        pass
    elif verify_data[u'method'] == u'DNS_TXT':
      try:
        import dns.resolver
        resolver = dns.resolver.Resolver()
        resolver.nameservers = [u'8.8.8.8', u'8.8.4.4']
        try:
          answers = resolver.query(a_domain, u'TXT')
          for answer in answers:
            print u'DNS Record: %s' % str(answer).replace(u'"', u'')
        except dns.resolver.NXDOMAIN:
          print u'ERROR: no such domain found in DNS!'
      except ImportError:
        pass
    return
  print u'SUCCESS!'
  print u'Verified:  %s' % verify_result[u'site'][u'identifier']
  print u'ID:  %s' % verify_result[u'id']
  print u'Type: %s' % verify_result[u'site'][u'type']
  print u'All Owners:'
  try:
    for owner in verify_result[u'owners']:
      print u' %s' % owner
  except KeyError:
    pass
  print
  print u'You can now add %s or it\'s subdomains as secondary or domain aliases of the %s G Suite Account.' % (a_domain, GC_Values[GC_DOMAIN])

def doInfoSiteVerification():
  verif = buildGAPIObject(GAPI_SITEVERIFICATION_API)
  checkForExtraneousArguments()
  sites = callGAPIitems(verif.webResource(), u'list', u'items')
  if len(sites) > 0:
    for site in sites:
      print u'Site: %s' % site[u'site'][u'identifier']
      print u'Type: %s' % site[u'site'][u'type']
      print u'Owners:'
      for owner in site[u'owners']:
        print u' %s' % owner
      print
  else:
    print u'No Sites Verified.'

GUARDIAN_STATES = [u'COMPLETE', u'PENDING', u'GUARDIAN_INVITATION_STATE_UNSPECIFIED']

def doInviteGuardian():
  croom = buildGAPIObject(GAPI_CLASSROOM_API)
  body = {u'invitedEmailAddress': getEmailAddress()}
  studentId = normalizeStudentGuardianEmailAddressOrUID(getString(OB_STUDENT_ITEM))
  checkForExtraneousArguments()
  try:
    result = callGAPI(croom.userProfiles().guardianInvitations(), u'create',
                      throw_reasons=[GAPI_NOT_FOUND, GAPI_INVALID_ARGUMENT, GAPI_BAD_REQUEST, GAPI_FORBIDDEN, GAPI_PERMISSION_DENIED, GAPI_ALREADY_EXISTS],
                      studentId=studentId, body=body)
    print u'Invited email %s as guardian of %s. Invite ID %s' % (result[u'invitedEmailAddress'], studentId, result[u'invitationId'])
  except (GAPI_notFound, GAPI_invalidArgument, GAPI_badRequest, GAPI_forbidden):
    entityUnknownWarning(u'Student', studentId, 0, 0)
  except GAPI_alreadyExists:
    stderrErrorMsg(u'Invited email %s as guardian of %s is a duplicate' % (body[u'invitedEmailAddress'], studentId))

def _cancelGuardianInvitation(croom, studentId, invitationId):
  try:
    result = callGAPI(croom.userProfiles().guardianInvitations(), u'patch',
                      throw_reasons=[GAPI_FORBIDDEN, GAPI_NOT_FOUND, GAPI_FAILED_PRECONDITION],
                      studentId=studentId, invitationId=invitationId, updateMask=u'state', body={u'state': u'COMPLETE'})
    print u'Cancelled PENDING guardian invitation for %s as guardian of %s' % (result[u'invitedEmailAddress'], studentId)
    return 0
  except GAPI_forbidden:
    entityUnknownWarning(u'Student', studentId, 0, 0)
    systemErrorExit(ENTITY_DOES_NOT_EXIST_RC, None)
  except GAPI_notFound:
    stderrErrorMsg(u'Guardian invitation %s for %s does not exist' % (invitationId, studentId))
  except GAPI_failedPrecondition:
    stderrErrorMsg(u'Guardian invitation %s for %s status is not PENDING' % (invitationId, studentId))
  return AC_FAILED_RC

def doCancelGuardianInvitation():
  croom = buildGAPIObject(GAPI_CLASSROOM_API)
  invitationId = getString(OB_GUARDIAN_INVITATION_ID)
  studentId = normalizeStudentGuardianEmailAddressOrUID(getString(OB_STUDENT_ITEM))
  checkForExtraneousArguments()
  status = _cancelGuardianInvitation(croom, studentId, invitationId)
  setSysExitRC(status)

def doDeleteGuardian():
  croom = buildGAPIObject(GAPI_CLASSROOM_API)
  invitationsOnly = False
  guardianId = normalizeStudentGuardianEmailAddressOrUID(getString(OB_GUARDIAN_ITEM))
  studentId = normalizeStudentGuardianEmailAddressOrUID(getString(OB_STUDENT_ITEM))
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg in [u'invitation', u'invitations']:
      invitationsOnly = True
    else:
      unknownArgumentExit()
  if not invitationsOnly:
    try:
      callGAPI(croom.userProfiles().guardians(), u'delete',
               throw_reasons=[GAPI_FORBIDDEN, GAPI_NOT_FOUND],
               studentId=studentId, guardianId=guardianId)
      print u'Deleted %s as a guardian of %s' % (guardianId, studentId)
      return
    except GAPI_forbidden:
      entityUnknownWarning(u'Student', studentId, 0, 0)
      systemErrorExit(ENTITY_DOES_NOT_EXIST_RC, None)
    except GAPI_notFound:
      pass
  # See if there's a pending invitation
  try:
    results = callGAPIpages(croom.userProfiles().guardianInvitations(), u'list', items=u'guardianInvitations',
                            throw_reasons=[GAPI_FORBIDDEN],
                            studentId=studentId, invitedEmailAddress=guardianId, states=[u'PENDING',])
    if len(results) > 0:
      for result in results:
        status = _cancelGuardianInvitation(croom, studentId, result[u'invitationId'])
      setSysExitRC(status)
    else:
      stderrErrorMsg(u'%s is not a guardian of %s and no invitation exists.' % (guardianId, studentId))
      setSysExitRC(AC_FAILED_RC)
  except GAPI_forbidden:
    entityUnknownWarning(u'Student', studentId, 0, 0)
    setSysExitRC(ENTITY_DOES_NOT_EXIST_RC)

def doPrintShowGuardians(csvFormat):
  croom = buildGAPIObject(GAPI_CLASSROOM_API)
  invitedEmailAddress = None
  studentIds = [u'-',]
  states = None
  service = croom.userProfiles().guardians()
  items = u'guardians'
  itemName = 'Guardians'
  if csvFormat:
    todrive = False
    csvRows = []
    titles = [u'studentEmail', u'studentId', u'invitedEmailAddress', u'guardianId']
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if csvFormat and myarg == u'todrive':
      todrive = True
    elif myarg == u'invitedguardian':
      invitedEmailAddress = getEmailAddress()
    elif myarg == u'student':
      studentIds = [normalizeStudentGuardianEmailAddressOrUID(getString(OB_STUDENT_ITEM))]
    elif myarg == u'invitations':
      service = croom.userProfiles().guardianInvitations()
      items = u'guardianInvitations'
      itemName = 'Guardian Invitations'
      titles = [u'studentEmail', u'studentId', u'invitedEmailAddress', u'invitationId']
      if states is None:
        states = GUARDIAN_STATES
    elif myarg == u'states':
      states = getString(OB_GUARDIAN_STATE_LIST).replace(u',', u' ').split()
    elif myarg in usergroup_types:
      studentIds = getUsersToModify(myarg, getString(OB_ENTITY))
    else:
      unknownArgumentExit()
  i = 0
  count = len(studentIds)
  for studentId in studentIds:
    i += 1
    studentId = normalizeStudentGuardianEmailAddressOrUID(studentId)
    kwargs = {u'invitedEmailAddress': invitedEmailAddress, u'studentId': studentId}
    if items == u'guardianInvitations':
      kwargs[u'states'] = states
    if studentId != u'-':
      if csvFormat:
        sys.stderr.write(u'Getting %s for %s%s' % (itemName, studentId, currentCountNL(i, count)))
    try:
      guardians = callGAPIpages(service, u'list', items=items,
                                throw_reasons=[GAPI_NOT_FOUND, GAPI_INVALID_ARGUMENT, GAPI_BAD_REQUEST, GAPI_FORBIDDEN, GAPI_PERMISSION_DENIED],
                                **kwargs)
      if not csvFormat:
        print u'Student: {0}, {1}:{2}'.format(studentId, itemName, currentCount(i, count))
        for guardian in guardians:
          showJSON(None, guardian, spacing=u'  ')
      else:
        for guardian in guardians:
          guardian[u'studentEmail'] = studentId
          addRowTitlesToCSVfile(flattenJSON(guardian), csvRows, titles)
    except (GAPI_notFound, GAPI_invalidArgument, GAPI_badRequest, GAPI_forbidden):
      entityUnknownWarning(u'Student', studentId, i, count)
    except GAPI_permissionDenied as e:
      sys.stderr.write(u'{0} guardians for Student {1} failed: {2}{3}'.format([u'show', u'print'][csvFormat], studentId, e.message, currentCountNL(i, count)))
  if csvFormat:
    sys.stderr.write(u'\n')
    writeCSVfile(csvRows, titles, itemName, todrive)

COURSE_STATE_OPTIONS_MAP = {
  u'active': u'ACTIVE',
  u'archived': u'ARCHIVED',
  u'provisioned': u'PROVISIONED',
  u'declined': u'DECLINED',
  }

def getCourseAttribute(myarg, body):
  if myarg == u'name':
    body[u'name'] = getString(OB_STRING)
  elif myarg == u'section':
    body[u'section'] = getString(OB_STRING)
  elif myarg == u'heading':
    body[u'descriptionHeading'] = getString(OB_STRING)
  elif myarg == u'description':
    body[u'description'] = getString(OB_STRING)
  elif myarg == u'room':
    body[u'room'] = getString(OB_STRING)
  elif myarg in [u'state', u'status']:
    body[u'courseState'] = getChoice(COURSE_STATE_OPTIONS_MAP, mapChoice=True)
  else:
    unknownArgumentExit()

def doCreateCourse():
  croom = buildGAPIObject(GAPI_CLASSROOM_API)
  body = {u'ownerId': u'me', u'name': u'Unknown Course'}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg in [u'alias', u'id']:
      body[u'id'] = getCourseAlias()
    elif myarg == u'teacher':
      body[u'ownerId'] = getEmailAddress()
    else:
      getCourseAttribute(myarg, body)
  result = callGAPI(croom.courses(), u'create', body=body)
  print u'Course: {0}, Course ID: {1}, Created'.format(result[u'name'], result[u'id'])

def doUpdateCourse():
  croom = buildGAPIObject(GAPI_CLASSROOM_API)
  courseId = getCourseId()
  body = {}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    getCourseAttribute(myarg, body)
  updateMask = u','.join(body.keys())
  body[u'id'] = courseId
  result = callGAPI(croom.courses(), u'patch', id=courseId, body=body, updateMask=updateMask)
  print u'Updated Course %s' % result[u'id']

def doDeleteCourse():
  croom = buildGAPIObject(GAPI_CLASSROOM_API)
  courseId = getCourseId()
  checkForExtraneousArguments()
  callGAPI(croom.courses(), u'delete', id=courseId)
  print u'Deleted Course %s' % courseId

def doInfoCourse():
  croom = buildGAPIObject(GAPI_CLASSROOM_API)
  courseId = getCourseId()
  checkForExtraneousArguments()
  info = callGAPI(croom.courses(), u'get', id=courseId)
  showJSON(None, info)
  teachers = callGAPIpages(croom.courses().teachers(), u'list', u'teachers', courseId=courseId)
  students = callGAPIpages(croom.courses().students(), u'list', u'students', courseId=courseId)
  try:
    aliases = callGAPIpages(croom.courses().aliases(), u'list', u'aliases', throw_reasons=[GAPI_NOT_IMPLEMENTED], courseId=courseId)
  except GAPI_notImplemented:
    aliases = []
  if aliases:
    print u'Aliases:'
    for alias in aliases:
      print u'  %s' % alias[u'alias'][2:]
  print u'Participants:'
  print u' Teachers:'
  for teacher in teachers:
    try:
      print convertUTF8(u'  %s - %s' % (teacher[u'profile'][u'name'][u'fullName'], teacher[u'profile'][u'emailAddress']))
    except KeyError:
      print convertUTF8(u'  %s' % teacher[u'profile'][u'name'][u'fullName'])
  print u' Students:'
  for student in students:
    try:
      print convertUTF8(u'  %s - %s' % (student[u'profile'][u'name'][u'fullName'], student[u'profile'][u'emailAddress']))
    except KeyError:
      print convertUTF8(u'  %s' % student[u'profile'][u'name'][u'fullName'])

def doPrintCourses():
  croom = buildGAPIObject(GAPI_CLASSROOM_API)
  todrive = False
  titles = [u'id',]
  csvRows = []
  teacherId = None
  studentId = None
  get_aliases = False
  delimiter = GC_Values[GC_CSV_OUTPUT_FIELD_DELIMITER]
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'teacher':
      teacherId = getEmailAddress()
    elif myarg == u'student':
      studentId = getEmailAddress()
    elif myarg == u'todrive':
      todrive = True
    elif myarg in [u'alias', u'aliases']:
      get_aliases = True
    elif myarg == u'delimiter':
      delimiter = getString(OB_STRING, minLen=1, maxLen=1)
    else:
      unknownArgumentExit()
  sys.stderr.write(u'Retrieving courses for organization (may take some time for large accounts)...\n')
  page_message = u'Got %%num_items%% courses...\n'
  all_courses = callGAPIpages(croom.courses(), u'list', u'courses', page_message=page_message, teacherId=teacherId, studentId=studentId)
  for course in all_courses:
    addRowTitlesToCSVfile(flattenJSON(course), csvRows, titles)
  if get_aliases:
    titles.append(u'Aliases')
    i = 0
    count = len(csvRows)
    for course in csvRows:
      i += 1
      sys.stderr.write(u'Getting aliases for course %s%s' % (course[u'id'], currentCountNL(i, count)))
      course_aliases = callGAPIpages(croom.courses().aliases(), u'list', u'aliases', courseId=course[u'id'])
      course[u'Aliases'] = delimiter.join([alias[u'alias'][2:] for alias in course_aliases])
  writeCSVfile(csvRows, titles, u'Courses', todrive)

ADD_REMOVE_PARTICIPANT_TYPES_MAP = {
  u'alias': u'alias',
  u'student': u'student',
  u'students': u'student',
  u'teacher': u'teacher',
  u'teachers': u'teacher',
  }
SYNC_PARTICIPANT_TYPES_MAP = {
  u'student': u'student',
  u'students': u'student',
  u'teacher': u'teacher',
  u'teachers': u'teacher',
  }
PARTICIPANT_ENTITY_NAME_MAP = {
  u'student': u'students',
  u'teacher': u'teachers',
  }

def doCourseAddParticipant(courseId):
  croom = buildGAPIObject(GAPI_CLASSROOM_API)
  noScopeCourseId = removeCourseIdScope(courseId)
  participant_type = getChoice(ADD_REMOVE_PARTICIPANT_TYPES_MAP, mapChoice=True)
  if participant_type == u'alias':
    body = {u'alias': addCourseIdScope(getString(OB_COURSE_ALIAS))}
    checkForExtraneousArguments()
    callGAPI(croom.courses().aliases(), u'create', courseId=courseId, body=body)
    print u'Added %s as an %s of course %s' % (removeCourseIdScope(body[u'alias']), participant_type, noScopeCourseId)
  else:
    body = {u'userId': getEmailAddress()}
    checkForExtraneousArguments()
    if participant_type == u'teacher':
      service = croom.courses().teachers()
    else:
      service = croom.courses().students()
    callGAPI(service, u'create', courseId=courseId, body=body)
    print u'Added %s as a %s of course %s' % (body[u'userId'], participant_type, noScopeCourseId)

def doCourseRemoveParticipant(courseId):
  croom = buildGAPIObject(GAPI_CLASSROOM_API)
  noScopeCourseId = removeCourseIdScope(courseId)
  participant_type = getChoice(ADD_REMOVE_PARTICIPANT_TYPES_MAP, mapChoice=True)
  if participant_type == u'alias':
    alias = addCourseIdScope(getString(OB_COURSE_ALIAS))
    checkForExtraneousArguments()
    callGAPI(croom.courses().aliases(), u'delete', courseId=courseId, alias=alias)
    print u'Removed %s as an %s of course %s' % (removeCourseIdScope(alias), participant_type, noScopeCourseId)
  else:
    userId = getEmailAddress()
    checkForExtraneousArguments()
    if participant_type == u'teacher':
      service = croom.courses().teachers()
    else:
      service = croom.courses().students()
    callGAPI(service, u'delete', courseId=courseId, userId=userId)
    print u'Removed %s as a %s of course %s' % (userId, participant_type, noScopeCourseId)

def doCourseSyncParticipants(courseId):
  participant_type = getChoice(SYNC_PARTICIPANT_TYPES_MAP, mapChoice=True)
  diff_entityType = getString(OB_ENTITY_TYPE)
  diff_entity = getString(OB_ENTITY)
  checkForExtraneousArguments()
  current_course_users = getUsersToModify(PARTICIPANT_ENTITY_NAME_MAP[participant_type], courseId)
  current_course_users = [x.lower() for x in current_course_users]
  if diff_entityType == u'courseparticipants':
    diff_entityType = participant_type
  diff_against_users = getUsersToModify(diff_entityType, diff_entity)
  print
  diff_against_users = [x.lower() for x in diff_against_users]
  to_add = list(set(diff_against_users) - set(current_course_users))
  to_remove = list(set(current_course_users) - set(diff_against_users))
  gam_commands = []
  for add_email in to_add:
    gam_commands.append([GAM_CMD, u'course', courseId, u'add', participant_type, add_email])
  for remove_email in to_remove:
    gam_commands.append([GAM_CMD, u'course', courseId, u'remove', participant_type, remove_email])
  run_batch(gam_commands)

def doPrintCourseParticipants():
  croom = buildGAPIObject(GAPI_CLASSROOM_API)
  todrive = False
  titles = [u'courseId',]
  csvRows = []
  courses = []
  teacherId = None
  studentId = None
  showMembers = u'all'
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg in [u'course', u'class']:
      courses.append(getCourseId())
    elif myarg == u'teacher':
      teacherId = getEmailAddress()
    elif myarg == u'student':
      studentId = getEmailAddress()
    elif myarg == u'todrive':
      todrive = True
    elif myarg == u'show':
      showMembers = getChoice([u'all', u'students', u'teachers'])
    else:
      unknownArgumentExit()
  if len(courses) == 0:
    sys.stderr.write(u'Retrieving courses for organization (may take some time for large accounts)...\n')
    page_message = u'Got %%num_items%% courses...\n'
    all_courses = callGAPIpages(croom.courses(), u'list', u'courses', page_message=page_message, teacherId=teacherId, studentId=studentId)
    for course in all_courses:
      courses.append(course[u'id'])
  else:
    all_courses = []
    for course in courses:
      all_courses.append(callGAPI(croom.courses(), u'get', id=course))
  y = 1
  num_courses = len(all_courses)
  for course in all_courses:
    course_id = course[u'id']
    if showMembers != u'students':
      teacher_message = u' got %%%%num_items%%%% teachers for course %s%s' % (course_id, currentCount(y, num_courses))
      teachers = callGAPIpages(croom.courses().teachers(), u'list', u'teachers', page_message=teacher_message, courseId=course_id)
    if showMembers != u'teachers':
      student_message = u' got %%%%num_items%%%% students for course %s%s' % (course_id, currentCount(y, num_courses))
      students = callGAPIpages(croom.courses().students(), u'list', u'students', page_message=student_message, courseId=course_id)
    for teacher in teachers:
      row = flattenJSON(teacher)
      row[u'courseId'] = course_id
      row[u'courseName'] = course[u'name']
      row[u'userRole'] = u'TEACHER'
      csvRows.append(row)
      for item in row:
        if item not in titles:
          titles.append(item)
    for student in students:
      row = flattenJSON(student)
      row[u'courseId'] = course_id
      row[u'courseName'] = course[u'name']
      row[u'userRole'] = u'STUDENT'
      csvRows.append(row)
      for item in row:
        if item not in titles:
          titles.append(item)
    y += 1
  writeCSVfile(csvRows, titles, u'Course Participants', todrive)

def encode_multipart(fields, files, boundary=None):
  def escape_quote(s):
    return s.replace('"', '\\"')

  def getFormDataLine(name, value, boundary):
    return '--{0}'.format(boundary), 'Content-Disposition: form-data; name="{0}"'.format(escape_quote(name)), '', str(value)

  if boundary is None:
    boundary = ''.join(random.choice(string.digits + string.ascii_letters) for i in range(30))
  lines = []
  for name, value in fields.items():
    if name == u'tags':
      for tag in value:
        lines.extend(getFormDataLine('tag', tag, boundary))
    else:
      lines.extend(getFormDataLine(name, value, boundary))
  for name, value in files.items():
    filename = value[u'filename']
    mimetype = value[u'mimetype']
    lines.extend((
      '--{0}'.format(boundary),
      'Content-Disposition: form-data; name="{0}"; filename="{1}"'.format(escape_quote(name), escape_quote(filename)),
      'Content-Type: {0}'.format(mimetype),
      '',
      value[u'content'],
    ))
  lines.extend((
    '--{0}--'.format(boundary),
    '',
  ))
  body = '\r\n'.join(lines)
  headers = {
    'Content-Type': 'multipart/form-data; boundary={0}'.format(boundary),
    'Content-Length': str(len(body)),
  }
  return (body, headers)

def doPrinterRegister():
  cp = buildGAPIObject(GAPI_CLOUDPRINT_API)
  form_fields = {u'name': u'GAM',
                 u'proxy': u'GAM',
                 u'uuid': cp._http.request.credentials.id_token[u'sub'],
                 u'manufacturer': __author__,
                 u'model': u'cp1',
                 u'gcp_version': u'2.0',
                 u'setup_url': GAM_URL,
                 u'support_url': u'https://groups.google.com/forum/#!forum/google-apps-manager',
                 u'update_url': GAM_RELEASES,
                 u'firmware': __version__,
                 u'semantic_state': {"version": "1.0", "printer": {"state": "IDLE",}},
                 u'use_cdd': True,
                 u'capabilities': {"version": "1.0",
                                   "printer": {"supported_content_type": [{"content_type": "application/pdf", "min_version": "1.5"},
                                                                          {"content_type": "image/jpeg"},
                                                                          {"content_type": "text/plain"}
                                                                         ],
                                               "copies": {"default": 1, "max": 100},
                                               "media_size": {"option": [{"name": "ISO_A4", "width_microns": 210000, "height_microns": 297000},
                                                                         {"name": "NA_LEGAL", "width_microns": 215900, "height_microns": 355600},
                                                                         {"name": "NA_LETTER", "width_microns": 215900, "height_microns": 279400, "is_default": True}
                                                                        ],
                                                             },
                                              },
                                  },
                 u'tags': [u'GAM', GAM_URL],
                }
  body, headers = encode_multipart(form_fields, {})
  #Get the printer first to make sure our OAuth access token is fresh
  callGAPI(cp.printers(), u'list')
  _, result = cp._http.request(uri='https://www.google.com/cloudprint/register', method='POST', body=body, headers=headers)
  result = checkCloudPrintResult(result)
  print u'Created printer %s' % result[u'printers'][0][u'id']

PRINTER_UPDATE_ITEMS_CHOICES_MAP = {
  u'currentquota': u'currentQuota',
  u'dailyquota': u'dailyQuota',
  u'defaultdisplayname': u'defaultDisplayName',
  u'description': u'description',
  u'displayname': u'displayName',
  u'firmware': u'firmware',
  u'gcpversion': u'gcpVersion',
  u'istosaccepted': u'isTosAccepted',
  u'manufacturer': u'manufacturer',
  u'model': u'model',
  u'name': u'name',
  u'ownerid': u'ownerId',
  u'proxy': u'proxy',
  u'public': u'public',
  u'quotaenabled': u'quotaEnabled',
  u'setupurl': u'setupUrl',
  u'status': u'status',
  u'supporturl': u'supportUrl',
  u'type': u'type',
  u'updateurl': u'updateUrl',
  u'uuid': u'uuid',
  }

def doUpdatePrinter():
  cp = buildGAPIObject(GAPI_CLOUDPRINT_API)
  printerId = getString(OB_PRINTER_ID)
  kwargs = {}
  while CL_argvI < CL_argvLen:
    myarg = getChoice(PRINTER_UPDATE_ITEMS_CHOICES_MAP, mapChoice=True)
    if myarg in [u'isTosAccepted', u'public', u'quotaEnabled']:
      value = getBoolean()
    elif myarg in [u'currentQuota', u'dailyQuota', u'status']:
      value = getInteger(minVal=0)
    else:
      value = getString(OB_STRING)
    kwargs[myarg] = value
  callGCP(cp.printers(), u'update',
          printerid=printerId, **kwargs)
  print u'Updated printer %s' % printerId

def doDeletePrinter():
  cp = buildGAPIObject(GAPI_CLOUDPRINT_API)
  printerId = getString(OB_PRINTER_ID)
  checkForExtraneousArguments()
  callGCP(cp.printers(), u'delete',
          printerid=printerId)

def doInfoPrinter():
  cp = buildGAPIObject(GAPI_CLOUDPRINT_API)
  printerId = getString(OB_PRINTER_ID)
  everything = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'everything':
      everything = True
    else:
      unknownArgumentExit()
  result = callGCP(cp.printers(), u'get',
                   printerid=printerId)
  printer_info = result[u'printers'][0]
  printer_info[u'createTime'] = datetime.datetime.fromtimestamp(int(printer_info[u'createTime'])/1000).strftime(u'%Y-%m-%d %H:%M:%S')
  printer_info[u'accessTime'] = datetime.datetime.fromtimestamp(int(printer_info[u'accessTime'])/1000).strftime(u'%Y-%m-%d %H:%M:%S')
  printer_info[u'updateTime'] = datetime.datetime.fromtimestamp(int(printer_info[u'updateTime'])/1000).strftime(u'%Y-%m-%d %H:%M:%S')
  printer_info[u'tags'] = u' '.join(printer_info[u'tags'])
  if not everything:
    del printer_info[u'capabilities']
    del printer_info[u'access']
  showJSON(None, printer_info)

def doPrintPrinters():
  cp = buildGAPIObject(GAPI_CLOUDPRINT_API)
  todrive = False
  titles = [u'id',]
  csvRows = []
  query = None
  printer_type = None
  connection_status = None
  extra_fields = None
  delimiter = GC_Values[GC_CSV_OUTPUT_FIELD_DELIMITER]
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'query':
      query = getString(OB_QUERY)
    elif myarg == u'type':
      printer_type = getString(OB_STRING)
    elif myarg == u'status':
      connection_status = getString(OB_STRING)
    elif myarg == u'extrafields':
      extra_fields = getString(OB_STRING)
    elif myarg == u'todrive':
      todrive = True
    elif myarg == u'delimiter':
      delimiter = getString(OB_STRING, minLen=1, maxLen=1)
    else:
      unknownArgumentExit()
  printers = callGCP(cp.printers(), u'list',
                     q=query, type=printer_type, connection_status=connection_status, extra_fields=extra_fields)
  for printer in printers[u'printers']:
    printer[u'createTime'] = datetime.datetime.fromtimestamp(int(printer[u'createTime'])/1000).strftime(u'%Y-%m-%d %H:%M:%S')
    printer[u'accessTime'] = datetime.datetime.fromtimestamp(int(printer[u'accessTime'])/1000).strftime(u'%Y-%m-%d %H:%M:%S')
    printer[u'updateTime'] = datetime.datetime.fromtimestamp(int(printer[u'updateTime'])/1000).strftime(u'%Y-%m-%d %H:%M:%S')
    printer[u'tags'] = delimiter.join(printer[u'tags'])
    addRowTitlesToCSVfile(flattenJSON(printer), csvRows, titles)
  writeCSVfile(csvRows, titles, u'Printers', todrive)

def getPrinterScope():
  scope = getString(OB_EMAIL_ADDRESS).lower()
  if scope != u'public':
    if scope.find(u'@') == -1:
      scope = u'/hd/domain/{0}'.format(scope)
    else:
      scope = normalizeEmailAddressOrUID(scope, noUid=True)
  return scope

PRINTER_ROLE_MAP = {
  u'manager': ROLE_MANAGER,
  u'owner': ROLE_OWNER,
  u'user': ROLE_USER,
}

def doPrinterAddACL(printerId):
  cp = buildGAPIObject(GAPI_CLOUDPRINT_API)
  role = getChoice(PRINTER_ROLE_MAP, mapChoice=True)
  scope = getPrinterScope()
  checkForExtraneousArguments()
  public = None
  skip_notification = True
  if scope.lower() == u'public':
    public = True
    scope = None
    roleForScope = None
    skip_notification = None
  else:
    public = None
    roleForScope = role
    skip_notification = True
  callGCP(cp.printers(), u'share',
          printerid=printerId, role=roleForScope, scope=scope, public=public, skip_notification=skip_notification)
  if scope is None:
    scope = u'public'
    roleForScope = ROLE_USER
  print u'Added %s %s' % (roleForScope, scope)

def doPrinterDeleteACL(printerId):
  cp = buildGAPIObject(GAPI_CLOUDPRINT_API)
  scope = getPrinterScope()
  checkForExtraneousArguments()
  if scope.lower() == u'public':
    public = True
    scope = None
  else:
    public = None
  callGCP(cp.printers(), u'unshare',
          printerid=printerId, scope=scope, public=public)
  if scope is None:
    scope = u'public'
  print u'Removed %s' % scope

def doPrinterShowACL(printerId):
  cp = buildGAPIObject(GAPI_CLOUDPRINT_API)
  checkForExtraneousArguments()
  printer_info = callGCP(cp.printers(), u'get',
                         printerid=printerId)
  for acl in printer_info[u'printers'][0][u'access']:
    if u'key' in acl:
      acl[u'accessURL'] = u'https://www.google.com/cloudprint/addpublicprinter.html?printerid=%s&key=%s' % (printerId, acl[u'key'])
    showJSON(None, acl)
    print

def doPrintJobCancel(jobId):
  cp = buildGAPIObject(GAPI_CLOUDPRINT_API)
  ssd = u'{"state": {"type": "ABORTED", "user_action_cause": {"action_code": "CANCELLED"}}}'
  callGCP(cp.jobs(), u'update',
          jobid=jobId, semantic_state_diff=ssd)
  print u'Print Job %s cancelled' % jobId

def doPrintJobDelete(jobId):
  cp = buildGAPIObject(GAPI_CLOUDPRINT_API)
  checkForExtraneousArguments()
  callGCP(cp.jobs(), u'delete',
          jobid=jobId)
  print u'Print Job %s deleted' % jobId

def doPrintJobResubmit(jobId):
  cp = buildGAPIObject(GAPI_CLOUDPRINT_API)
  printerId = getString(OB_PRINTER_ID)
  checkForExtraneousArguments()
  ssd = u'{"state": {"type": "HELD"}}'
  result = callGCP(cp.jobs(), u'update',
                   jobid=jobId, semantic_state_diff=ssd)
  ticket = callGCP(cp.jobs(), u'getticket',
                   jobid=jobId, use_cjt=True)
  result = callGCP(cp.jobs(), u'resubmit',
                   printerid=printerId, jobid=jobId, ticket=ticket)
  print u'Success resubmitting %s as job %s to printer %s' % (jobId, result[u'job'][u'id'], printerId)

PRINTJOB_STATUS_MAP = {
  u'done': u'DONE',
  u'error': u'ERROR',
  u'held': u'HELD',
  u'inprogress': u'IN_PROGRESS',
  u'queued': u'QUEUED',
  u'submitted': u'SUBMITTED',
  }
PRINTJOB_ASCENDINGORDER_MAP = {
  u'createtime': u'CREATE_TIME',
  u'status': u'STATUS',
  u'title': u'TITLE',
  }
PRINTJOB_DESCENDINGORDER_MAP = {
  u'CREATE_TIME': u'CREATE_TIME_DESC',
  u'STATUS':  u'STATUS_DESC',
  u'TITLE': u'TITLE_DESC',
  }

PRINTJOBS_DEFAULT_JOB_LIMIT = 25
PRINTJOBS_DEFAULT_MAX_RESULTS = 100

def initPrintjobListParameters():
  return {u'older_or_newer': 0,
          u'age': None,
          u'ascDesc': None,
          u'sortorder': None,
          u'owner': None,
          u'query': None,
          u'status': None,
          u'jobLimit': PRINTJOBS_DEFAULT_JOB_LIMIT,
         }

def getPrintjobListParameters(myarg, parameters):
  if myarg == u'olderthan':
    parameters[u'older_or_newer'] = 1
    parameters[u'age'] = getAgeTime()
  elif myarg == u'newerthan':
    parameters[u'older_or_newer'] = -1
    parameters[u'age'] = getAgeTime()
  elif myarg == u'query':
    parameters[u'query'] = getString(OB_QUERY)
  elif myarg == u'status':
    parameters[u'status'] = getChoice(PRINTJOB_STATUS_MAP, mapChoice=True)
  elif myarg in SORTORDER_CHOICES_MAP:
    parameters[u'ascDesc'] = SORTORDER_CHOICES_MAP[myarg]
  elif myarg == u'orderby':
    parameters[u'sortorder'] = getChoice(PRINTJOB_ASCENDINGORDER_MAP, mapChoice=True)
  elif myarg in [u'owner', u'user']:
    parameters[u'owner'] = getEmailAddress(noUid=True)
  elif myarg == u'limit':
    parameters[u'jobLimit'] = getInteger(minVal=0)
  else:
    unknownArgumentExit()

def doPrintJobFetch(printerId):
  cp = buildGAPIObject(GAPI_CLOUDPRINT_API)
  if printerId == u'any':
    printerId = None
  parameters = initPrintjobListParameters()
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    getPrintjobListParameters(myarg, parameters)
  if parameters[u'sortorder'] and (parameters[u'ascDesc'] == u'DESCENDING'):
    parameters[u'sortorder'] = PRINTJOB_DESCENDINGORDER_MAP[parameters[u'sortorder']]
  if printerId:
    callGCP(cp.printers(), u'get',
            printerid=printerId)
  valid_chars = u'-_.() abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789'
  ssd = u'{"state": {"type": "DONE"}}'
  jobCount = offset = 0
  while True:
    if parameters[u'jobLimit'] == 0:
      limit = PRINTJOBS_DEFAULT_MAX_RESULTS
    else:
      limit = min(PRINTJOBS_DEFAULT_MAX_RESULTS, parameters[u'jobLimit']-jobCount)
      if limit == 0:
        break
    result = callGCP(cp.jobs(), u'list',
                     printerid=printerId, q=parameters[u'query'], status=parameters[u'status'], sortorder=parameters[u'sortorder'],
                     owner=parameters[u'owner'], offset=offset, limit=limit)
    newJobs = result[u'range'][u'jobsCount']
    if newJobs == 0:
      break
    jobCount += newJobs
    offset += newJobs
    for job in result[u'jobs']:
      createTime = int(job[u'createTime'])
      if parameters[u'older_or_newer'] > 0:
        if createTime > parameters[u'age']:
          continue
      elif parameters[u'older_or_newer'] < 0:
        if createTime < parameters[u'age']:
          continue
      fileUrl = job[u'fileUrl']
      jobId = job[u'id']
      fileName = u'{0}-{1}'.format(u''.join(c if c in valid_chars else u'_' for c in job[u'title']), jobId)
      _, content = cp._http.request(fileUrl, method='GET')
      if writeFile(fileName, content, continueOnError=True):
#        ticket = callGCP(cp.jobs(), u'getticket',
#                         jobid=jobId, use_cjt=True)
        result = callGCP(cp.jobs(), u'update',
                         jobid=jobId, semantic_state_diff=ssd)
        print u'Printed job %s to %s' % (jobId, fileName)
  if jobCount == 0:
    print u'No print jobs.'

def doPrintPrintJobs():
  cp = buildGAPIObject(GAPI_CLOUDPRINT_API)
  todrive = False
  titles = [u'printerid', u'id']
  csvRows = []
  printerid = None
  parameters = initPrintjobListParameters()
  delimiter = GC_Values[GC_CSV_OUTPUT_FIELD_DELIMITER]
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'todrive':
      todrive = True
    elif myarg in [u'printer', u'printerid']:
      printerid = getString(OB_PRINTER_ID)
    elif myarg == u'delimiter':
      delimiter = getString(OB_STRING, minLen=1, maxLen=1)
    else:
      getPrintjobListParameters(myarg, parameters)
  if parameters[u'sortorder'] and (parameters[u'ascDesc'] == u'DESCENDING'):
    parameters[u'sortorder'] = PRINTJOB_DESCENDINGORDER_MAP[parameters[u'sortorder']]
  if printerid:
    callGCP(cp.printers(), u'get',
            printerid=printerid)
  jobCount = offset = 0
  while True:
    if parameters[u'jobLimit'] == 0:
      limit = PRINTJOBS_DEFAULT_MAX_RESULTS
    else:
      limit = min(PRINTJOBS_DEFAULT_MAX_RESULTS, parameters[u'jobLimit']-jobCount)
      if limit == 0:
        break
    result = callGCP(cp.jobs(), u'list',
                     printerid=printerid, q=parameters[u'query'], status=parameters[u'status'], sortorder=parameters[u'sortorder'],
                     owner=parameters[u'owner'], offset=offset, limit=limit)
    newJobs = result[u'range'][u'jobsCount']
    if newJobs == 0:
      break
    jobCount += newJobs
    offset += newJobs
    for job in result[u'jobs']:
      createTime = int(job[u'createTime'])
      if parameters[u'older_or_newer'] > 0:
        if createTime > parameters[u'age']:
          continue
      elif parameters[u'older_or_newer'] < 0:
        if createTime < parameters[u'age']:
          continue
      job[u'createTime'] = datetime.datetime.fromtimestamp(int(job[u'createTime'])/1000).strftime(u'%Y-%m-%d %H:%M:%S')
      job[u'updateTime'] = datetime.datetime.fromtimestamp(int(job[u'updateTime'])/1000).strftime(u'%Y-%m-%d %H:%M:%S')
      job[u'tags'] = delimiter.join(job[u'tags'])
      addRowTitlesToCSVfile(flattenJSON(job), csvRows, titles)
  writeCSVfile(csvRows, titles, u'Print Jobs', todrive)

def doPrintJobSubmit(printerId):
  cp = buildGAPIObject(GAPI_CLOUDPRINT_API)
  content = getString(OB_STRING)
  form_fields = {u'printerid': printerId,
                 u'title': content,
                 u'ticket': u'{"version": "1.0"}',
                 u'tags': [u'GAM', GAM_URL]}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'tag':
      form_fields[u'tags'].append(getString(OB_STRING))
    elif myarg in [u'name', u'title']:
      form_fields[u'title'] = getString(OB_STRING)
    else:
      unknownArgumentExit()
  form_files = {}
  if content[:4] == u'http':
    form_fields[u'content'] = content
    form_fields[u'contentType'] = u'url'
  else:
    filepath = content
    content = os.path.basename(content)
    mimetype = mimetypes.guess_type(filepath)[0]
    if mimetype is None:
      mimetype = u'application/octet-stream'
    filecontent = readFile(filepath)
    form_files[u'content'] = {u'filename': content, u'content': filecontent, u'mimetype': mimetype}
  #result = callGAPI(cp.printers(), u'submit', body=body)
  body, headers = encode_multipart(form_fields, form_files)
  #Get the printer first to make sure our OAuth access token is fresh
  callGCP(cp.printers(), u'get',
          printerid=printerId)
  _, result = cp._http.request(uri='https://www.google.com/cloudprint/submit', method='POST', body=body, headers=headers)
  result = checkCloudPrintResult(result)
  print u'Submitted print job %s' % result[u'job'][u'id']

def deleteASP(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  codeId = getString(OB_ASP_ID)
  checkForExtraneousArguments()
  for user in users:
    user = normalizeEmailAddressOrUID(user)
    callGAPI(cd.asps(), u'delete', userKey=user, codeId=codeId)
    print u'deleted ASP %s for %s' % (codeId, user)

def showASPs(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user = normalizeEmailAddressOrUID(user)
    asps = callGAPIitems(cd.asps(), u'list', u'items', userKey=user)
    if len(asps) > 0:
      print u'User: {0}, Application-Specific Passwords:{1}'.format(user, currentCount(i, count))
      for asp in asps:
        if asp[u'creationTime'] == u'0':
          created_date = u'Unknown'
        else:
          created_date = datetime.datetime.fromtimestamp(int(asp[u'creationTime'])/1000).strftime(u'%Y-%m-%d %H:%M:%S')
        if asp[u'lastTimeUsed'] == u'0':
          used_date = u'Never'
        else:
          used_date = datetime.datetime.fromtimestamp(int(asp[u'lastTimeUsed'])/1000).strftime(u'%Y-%m-%d %H:%M:%S')
        print u'  ID: %s\n    Name: %s\n    Created: %s\n    Last Used: %s\n' % (asp[u'codeId'], asp[u'name'], created_date, used_date)
    else:
      print u'User: {0}, No Application-Specific Passwords:{1}'.format(user, currentCount(i, count))

def _showBackupCodes(user, codes, i, count):
  jcount = len(codes)
  print u'User: {0}, Backup Verification Codes:{1}'.format(user, currentCount(i, count))
  if jcount > 0:
    j = 0
    for code in codes:
      j += 1
      print u'  {0:2}: {1}'.format(j, code[u'verificationCode'])

def showBackupCodes(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user = normalizeEmailAddressOrUID(user)
    try:
      codes = callGAPIitems(cd.verificationCodes(), u'list', u'items', throw_reasons=[GAPI_INVALID_ARGUMENT, GAPI_INVALID], userKey=user)
    except (GAPI_invalidArgument, GAPI_invalid):
      codes = []
    _showBackupCodes(user, codes, i, count)

def updateBackupCodes(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user = normalizeEmailAddressOrUID(user)
    callGAPI(cd.verificationCodes(), u'generate', userKey=user)
    codes = callGAPIitems(cd.verificationCodes(), u'list', u'items', userKey=user)
    _showBackupCodes(user, codes, i, count)

def deleteBackupCodes(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  checkForExtraneousArguments()
  for user in users:
    user = normalizeEmailAddressOrUID(user)
    try:
      callGAPI(cd.verificationCodes(), u'invalidate', soft_errors=True, throw_reasons=[GAPI_INVALID], userKey=user)
    except GAPI_invalid:
      print u'No 2SV backup codes for %s' % user
      continue
    print u'2SV backup codes for %s invalidated' % user

def normalizeCalendarId(calendarId, user):
  if calendarId.lower() != u'primary':
    return normalizeEmailAddressOrUID(calendarId)
  return user

CALENDAR_MIN_COLOR_INDEX = 1
CALENDAR_MAX_COLOR_INDEX = 24

CALENDAR_EVENT_MIN_COLOR_INDEX = 1
CALENDAR_EVENT_MAX_COLOR_INDEX = 11

CALENDAR_REMINDER_METHODS = [u'email', u'sms', u'popup',]
CALENDAR_NOTIFICATION_METHODS = [u'email', u'sms',]
CALENDAR_NOTIFICATION_TYPES_MAP = {
  u'eventcreation': u'eventCreation',
  u'eventchange': u'eventChange',
  u'eventcancellation': u'eventCancellation',
  u'eventresponse': u'eventResponse',
  u'agenda': u'agenda',
  }

def getCalendarAttributes(body):
  colorRgbFormat = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'selected':
      body[u'selected'] = getBoolean()
    elif myarg == u'hidden':
      body[u'hidden'] = getBoolean()
    elif myarg == u'summary':
      body[u'summaryOverride'] = getString(OB_STRING)
    elif myarg in [u'colorindex', u'colorid']:
      body[u'colorId'] = str(getInteger(CALENDAR_MIN_COLOR_INDEX, CALENDAR_MAX_COLOR_INDEX))
    elif myarg == u'backgroundcolor':
      body[u'backgroundColor'] = getColorHexAttribute()
      body.setdefault(u'foregroundColor', u'#000000')
      colorRgbFormat = True
    elif myarg == u'foregroundcolor':
      body[u'foregroundColor'] = getColorHexAttribute()
      colorRgbFormat = True
    elif myarg == u'reminder':
      body.setdefault(u'defaultReminders', [])
      if not checkArgumentPresent(CLEAR_NONE_ARGUMENT):
        body[u'defaultReminders'].append(getCalendarReminder(True))
    elif myarg == u'notification':
      body.setdefault(u'notificationSettings', {u'notifications': []})
      method = getChoice(CALENDAR_NOTIFICATION_METHODS+CLEAR_NONE_ARGUMENT)
      if method not in CLEAR_NONE_ARGUMENT:
        body[u'notificationSettings'][u'notifications'].append({u'method': method,
                                                                u'type': getChoice(CALENDAR_NOTIFICATION_TYPES_MAP, mapChoice=True)})
    else:
      unknownArgumentExit()
  return colorRgbFormat

def addCalendar(users):
  calendarId = getEmailAddress()
  body = {u'id': calendarId, u'selected': True, u'hidden': False}
  colorRgbFormat = getCalendarAttributes(body)
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, cal = buildCalendarGAPIObject(user)
    if not cal:
      continue
    print u"Subscribing %s to %s calendar%s" % (user, calendarId, currentCount(i, count))
    callGAPI(cal.calendarList(), u'insert', body=body, colorRgbFormat=colorRgbFormat)

def updateCalendar(users):
  calendarId = getString(OB_EMAIL_ADDRESS)
  body = {}
  colorRgbFormat = getCalendarAttributes(body)
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, cal = buildCalendarGAPIObject(user)
    if not cal:
      continue
    calId = normalizeCalendarId(calendarId, user)
    print u"Updating %s's subscription to calendar %s%s" % (user, calId, currentCount(i, count))
    callGAPI(cal.calendarList(), u'update', calendarId=calId, body=body, colorRgbFormat=colorRgbFormat)

def deleteCalendar(users):
  buildGAPIObject(GAPI_CALENDAR_API)
  calendarId = getEmailAddress()
  checkForExtraneousArguments()
  for user in users:
    user, cal = buildCalendarGAPIObject(user)
    if not cal:
      continue
    callGAPI(cal.calendarList(), u'delete', calendarId=calendarId)

def _showCalendar(userCalendar, j, jcount):
  print u'  Calendar: {0}{1}'.format(userCalendar[u'id'], currentCount(j, jcount))
  print convertUTF8(u'    Summary: {0}'.format(userCalendar.get(u'summaryOverride', userCalendar[u'summary'])))
  print convertUTF8(u'    Description: {0}'.format(userCalendar.get(u'description', u'')))
  print u'    Access Level: {0}'.format(userCalendar[u'accessRole'])
  print u'    Timezone: {0}'.format(userCalendar[u'timeZone'])
  print convertUTF8(u'    Location: {0}'.format(userCalendar.get(u'location', u'')))
  print u'    Hidden: {0}'.format(userCalendar.get(u'hidden', u'False'))
  print u'    Selected: {0}'.format(userCalendar.get(u'selected', u'False'))
  print u'    Color ID: {0}, Background Color: {1}, Foreground Color: {2}'.format(userCalendar[u'colorId'], userCalendar[u'backgroundColor'], userCalendar[u'foregroundColor'])
  print u'    Default Reminders:'
  for reminder in userCalendar.get(u'defaultReminders', []):
    print u'      Method: {0}, Minutes: {1}'.format(reminder[u'method'], reminder[u'minutes'])
  print u'    Notifications:'
  if u'notificationSettings' in userCalendar:
    for notification in userCalendar[u'notificationSettings'].get(u'notifications', []):
      print u'      Method: {0}, Type: {1}'.format(notification[u'method'], notification[u'type'])

def infoCalendar(users):
  buildGAPIObject(GAPI_CALENDAR_API)
  calendarId = getEmailAddress()
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, cal = buildCalendarGAPIObject(user)
    if not cal:
      continue
    result = callGAPI(cal.calendarList(), u'get',
                      soft_errors=True,
                      calendarId=calendarId)
    if result:
      print u'User: {0}, Calendar:{1}'.format(user, currentCount(i, count))
      _showCalendar(result, 1, 1)

def printShowCalendars(users, csvFormat):
  if csvFormat:
    todrive = False
    titles = []
    csvRows = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if csvFormat and myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, cal = buildCalendarGAPIObject(user)
    if not cal:
      continue
    result = callGAPIpages(cal.calendarList(), u'list', u'items')
    jcount = len(result)
    if not csvFormat:
      print u'User: {0}, Calendars:{1}'.format(user, currentCount(i, count))
      if jcount == 0:
        continue
      j = 0
      for userCalendar in result:
        j += 1
        _showCalendar(userCalendar, j, jcount)
    else:
      if jcount == 0:
        continue
      for userCalendar in result:
        row = {u'primaryEmail': user}
        addRowTitlesToCSVfile(flattenJSON(userCalendar, flattened=row), csvRows, titles)
  if csvFormat:
    sortCSVTitles([u'primaryEmail', u'id'], titles)
    writeCSVfile(csvRows, titles, u'Calendars', todrive)

def showCalSettings(users):
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, cal = buildCalendarGAPIObject(user)
    if not cal:
      continue
    feed = callGAPIpages(cal.settings(), u'list', u'items')
    print u'User: {0}, Calendar Settings:{1}'.format(user, currentCount(i, count))
    settings = {}
    for setting in feed:
      settings[setting[u'id']] = setting[u'value']
    for attr, value in sorted(settings.items()):
      print u'  {0}: {1}'.format(attr, value)

def updateCalendarAttendees(users):
  do_it = True
  allevents = False
  start_date = end_date = None
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'csv':
      csv_file = getString(OB_FILE_NAME)
    elif myarg == u'dryrun':
      do_it = False
    elif myarg == u'start':
      start_date = getYYYYMMDD()
    elif myarg == u'end':
      end_date = getYYYYMMDD()
    elif myarg == u'allevents':
      allevents = True
    else:
      unknownArgumentExit()
  if not csv_file:
    usageErrorExit(u'csv <Filename> required')
  attendee_map = {}
  f = openFile(csv_file)
  csvFile = csv.reader(f)
  for row in csvFile:
    attendee_map[row[0].lower()] = row[1].lower()
  closeFile(f)
  for user in users:
    sys.stdout.write(u'Checking user %s\n' % user)
    user, cal = buildCalendarGAPIObject(user)
    if not cal:
      continue
    page_token = None
    while True:
      events_page = callGAPI(cal.events(), u'list', calendarId=user, pageToken=page_token, timeMin=start_date, timeMax=end_date, showDeleted=False, showHiddenInvitations=False)
      print u'Got %s items' % len(events_page.get(u'items', []))
      for event in events_page.get(u'items', []):
        if event[u'status'] == u'cancelled':
          #print u' skipping cancelled event'
          continue
        try:
          event_summary = convertUTF8(event[u'summary'])
        except (KeyError, UnicodeEncodeError, UnicodeDecodeError):
          event_summary = event[u'id']
        try:
          if not allevents and event[u'organizer'][u'email'].lower() != user:
            #print u' skipping not-my-event %s' % event_summary
            continue
        except KeyError:
          pass # no email for organizer
        needs_update = False
        try:
          for attendee in event[u'attendees']:
            try:
              if attendee[u'email'].lower() in attendee_map:
                old_email = attendee[u'email'].lower()
                new_email = attendee_map[attendee[u'email'].lower()]
                print u' SWITCHING attendee %s to %s for %s' % (old_email, new_email, event_summary)
                event[u'attendees'].remove(attendee)
                event[u'attendees'].append({u'email': new_email})
                needs_update = True
            except KeyError: # no email for that attendee
              pass
        except KeyError:
          continue # no attendees
        if needs_update:
          body = {}
          body[u'attendees'] = event[u'attendees']
          print u'UPDATING %s' % event_summary
          if do_it:
            callGAPI(cal.events(), u'patch', calendarId=user, eventId=event[u'id'], sendNotifications=False, body=body)
          else:
            print u' not pulling the trigger.'
        #else:
        #  print u' no update needed for %s' % event_summary
      try:
        page_token = events_page[u'nextPageToken']
      except KeyError:
        break

def transferSecCals(users):
  target_user = getEmailAddress()
  addBody = {u'role': u'owner', u'scope': {u'type': u'user', u'value': target_user}}
  remove_source_user = True
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'keepuser':
      remove_source_user = False
    else:
      unknownArgumentExit()
  if remove_source_user:
    target_user, target_cal = buildCalendarGAPIObject(target_user)
    if not target_cal:
      return
  for user in users:
    user, source_cal = buildCalendarGAPIObject(user)
    if not source_cal:
      continue
    source_calendars = callGAPIpages(source_cal.calendarList(), u'list', u'items', minAccessRole=u'owner', showHidden=True, fields=u'items(id),nextPageToken')
    for source_cal in source_calendars:
      calendarId = source_cal[u'id']
      if calendarId.find(u'@group.calendar.google.com') != -1:
        callGAPI(source_cal.acl(), u'insert',
                 calendarId=calendarId, body=addBody)
        if remove_source_user:
          ruleId = u'{0}:{1}'.format(u'user', user)
          callGAPI(target_cal.acl(), u'delete',
                   calendarId=calendarId, ruleId=ruleId)

def doDriveSearch(drive, query=None):
  sys.stderr.write(u'Searching for files with query: "{0}"...\n'.format(query))
  page_message = u' got %%total_items%% files...\n'
  files = callGAPIpages(drive.files(), u'list', DRIVE_FILES_LIST,
                        page_message=page_message,
                        q=query, fields=u'nextPageToken,{0}(id)'.format(DRIVE_FILES_LIST), maxResults=GC_Values[GC_DRIVE_MAX_RESULTS])
  return [f_file[u'id'] for f_file in files]

def cleanFileIDsList(fileIdSelection, fileIds):
  fileIdSelection[u'fileIds'] = []
  fileIdSelection[u'root'] = []
  i = 0
  for fileId in fileIds:
    if fileId[:8].lower() == u'https://' or fileId[:7].lower() == u'http://':
      loc = fileId.find(u'/d/')
      if loc > 0:
        fileId = fileId[loc+3:]
        loc = fileId.find(u'/')
        if loc != -1:
          fileId = fileId[:loc]
      else:
        loc = fileId.find(u'/folderview?id=')
        if loc > 0:
          fileId = fileId[loc+15:]
          loc = fileId.find(u'&')
          if loc != -1:
            fileId = fileId[:loc]
        else:
          continue
    elif fileId.lower() == u'root':
      fileIdSelection[u'root'].append(i)
    fileIdSelection[u'fileIds'].append(fileId)
    i += 1

def initDriveFileEntity():
  return {u'fileIds': [], u'query': None, u'root': []}

def getDriveFileEntity():
  fileIdSelection = initDriveFileEntity()
  myarg = getString(OB_DRIVE_FILE_ID, checkBlank=True)
  mycmd = myarg.lower()
  if mycmd == u'id':
    cleanFileIDsList(fileIdSelection, getStringReturnInList(OB_DRIVE_FILE_ID))
  elif mycmd[:3] == u'id:':
    cleanFileIDsList(fileIdSelection, [myarg[3:]])
  elif mycmd == u'ids':
    cleanFileIDsList(fileIdSelection, getString(OB_DRIVE_FILE_ID).replace(u',', u' ').split())
  elif mycmd[:4] == u'ids:':
    cleanFileIDsList(fileIdSelection, myarg[4:].replace(u',', u' ').split())
  elif mycmd == u'query':
    fileIdSelection[u'query'] = getString(OB_QUERY)
  elif mycmd[:6] == u'query:':
    fileIdSelection[u'query'] = myarg[6:]
  elif mycmd == u'drivefilename':
    fileIdSelection[u'query'] = ME_IN_OWNERS_AND+u"{0} = '{1}'".format(DRIVE_FILE_NAME, getString(OB_DRIVE_FILE_NAME))
  elif mycmd[:14] == u'drivefilename:':
    fileIdSelection[u'query'] = ME_IN_OWNERS_AND+u"{0} = '{1}'".format(DRIVE_FILE_NAME, myarg[14:])
  elif mycmd == u'anydrivefilename':
    fileIdSelection[u'query'] = u"{0} = '{1}'".format(DRIVE_FILE_NAME, getString(OB_DRIVE_FILE_NAME))
  elif mycmd[:14] == u'anydrivefilename:':
    fileIdSelection[u'query'] = u"{0} = '{1}'".format(DRIVE_FILE_NAME, myarg[17:])
  elif mycmd == u'root':
    cleanFileIDsList(fileIdSelection, [mycmd,])
  else:
    cleanFileIDsList(fileIdSelection, [myarg,])
  return fileIdSelection

def validateUserGetFileIDs(user, i, count, fileIdSelection, body, parameters, drive=None):
  if not drive:
    user, drive = buildDriveGAPIObject(user)
    if not drive:
      return (user, None, 0)
  if parameters[DFA_PARENTQUERY]:
    more_parents = doDriveSearch(drive, query=parameters[DFA_PARENTQUERY])
    if more_parents is None:
      setSysExitRC(NO_ENTITIES_FOUND)
      return (user, None, 0)
    body.setdefault(u'parents', [])
    for a_parent in more_parents:
      body[u'parents'].append({u'id': a_parent})
  if fileIdSelection[u'query']:
    fileIdSelection[u'fileIds'] = doDriveSearch(drive, query=fileIdSelection[u'query'])
    if fileIdSelection[u'fileIds'] is None:
      return (user, None, 0)
  elif fileIdSelection[u'root']:
    try:
      rootFolderId = callGAPI(drive.about(), u'get',
                              throw_reasons=GAPI_DRIVE_THROW_REASONS,
                              fields=u'rootFolderId')[u'rootFolderId']
    except (GAPI_serviceNotAvailable, GAPI_authError):
      entityServiceNotApplicableWarning(u'User', user, i, count)
      return (user, None, 0)
    for j in fileIdSelection[u'root']:
      fileIdSelection[u'fileIds'][j] = rootFolderId
  l = len(fileIdSelection[u'fileIds'])
  if l == 0:
    setSysExitRC(NO_ENTITIES_FOUND)
  return (user, drive, l)

DRIVEFILE_LABEL_CHOICES_MAP = {
  u'restricted': u'restricted',
  u'restrict': u'restricted',
  u'starred': u'starred',
  u'star': u'starred',
  u'trashed': u'trashed',
  u'trash': u'trashed',
  u'viewed': u'viewed',
  u'view': u'viewed',
  }

MIMETYPE_CHOICES_MAP = {
  u'gdoc': MIMETYPE_GA_DOCUMENT,
  u'gdocument': MIMETYPE_GA_DOCUMENT,
  u'gdrawing': MIMETYPE_GA_DRAWING,
  u'gfolder': MIMETYPE_GA_FOLDER,
  u'gdirectory': MIMETYPE_GA_FOLDER,
  u'gform': MIMETYPE_GA_FORM,
  u'gfusion': MIMETYPE_GA_FUSIONTABLE,
  u'gpresentation': MIMETYPE_GA_PRESENTATION,
  u'gscript': MIMETYPE_GA_SCRIPT,
  u'gsite': MIMETYPE_GA_SITES,
  u'gsheet': MIMETYPE_GA_SPREADSHEET,
  u'gspreadsheet': MIMETYPE_GA_SPREADSHEET,
  }

def initializeDriveFileAttributes():
  return ({}, {DFA_LOCALFILEPATH: None, DFA_LOCALFILENAME: None, DFA_LOCALMIMETYPE: None,
               DFA_CONVERT: None, DFA_OCR: None, DFA_OCRLANGUAGE: None,
               DFA_PARENTQUERY: None, DFA_ADD_PARENTS: [], DFA_REMOVE_PARENTS: []})

def getDriveFileAttribute(body, parameters, myarg, update):
  if myarg == u'localfile':
    parameters[DFA_LOCALFILEPATH] = getString(OB_FILE_NAME)
    try:
      f = open(os.path.expanduser(parameters[DFA_LOCALFILEPATH]), u'rb')
      f.close()
    except IOError as e:
      putArgumentBack()
      usageErrorExit(u'{0}: {1}'.format(parameters[DFA_LOCALFILEPATH], e.strerror))
    parameters[DFA_LOCALFILENAME] = os.path.basename(parameters[DFA_LOCALFILEPATH])
    body.setdefault(DRIVE_FILE_NAME, parameters[DFA_LOCALFILENAME])
    body[u'mimeType'] = mimetypes.guess_type(parameters[DFA_LOCALFILEPATH])[0]
    if body[u'mimeType'] is None:
      body[u'mimeType'] = u'application/octet-stream'
    parameters[DFA_LOCALMIMETYPE] = body[u'mimeType']
  elif myarg == u'convert':
    parameters[DFA_CONVERT] = True
  elif myarg == u'ocr':
    parameters[DFA_OCR] = True
  elif myarg == u'ocrlanguage':
    parameters[DFA_OCRLANGUAGE] = getChoice(LANGUAGE_CODES_MAP, mapChoice=True)
  elif myarg in DRIVEFILE_LABEL_CHOICES_MAP:
    body.setdefault(u'labels', {})
    if update:
      body[u'labels'][DRIVEFILE_LABEL_CHOICES_MAP[myarg]] = getBoolean()
    else:
      body[u'labels'][DRIVEFILE_LABEL_CHOICES_MAP[myarg]] = True
  elif myarg in [u'lastviewedbyme', u'lastviewedbyuser', u'lastviewedbymedate', u'lastviewedbymetime']:
    body[u'lastViewedByMeDate'] = getFullTime()
  elif myarg in [u'modifieddate', u'modifiedtime']:
    body[u'modifiedDate'] = getFullTime()
  elif myarg == u'description':
    body[u'description'] = getString(OB_STRING)
  elif myarg == u'mimetype':
    body[u'mimeType'] = getChoice(MIMETYPE_CHOICES_MAP, mapChoice=True)
  elif myarg == u'parentid':
    body.setdefault(u'parents', [])
    body[u'parents'].append({u'id': getString(OB_DRIVE_FOLDER_ID)})
  elif myarg == u'parentname':
    parameters[DFA_PARENTQUERY] = u'"me" in owners and mimeType = "%s" and title = "%s"' % (MIMETYPE_GA_FOLDER, getString(OB_DRIVE_FOLDER_NAME))
  elif myarg == u'addparents':
    parameters[DFA_ADD_PARENTS].extend(getString(OB_DRIVE_FOLDER_ID).replace(u',', u' ').split())
  elif myarg == u'removeparents':
    parameters[DFA_REMOVE_PARENTS].extend(getString(OB_DRIVE_FOLDER_ID).replace(u',', u' ').split())
  elif myarg == u'writerscantshare':
    body[u'writersCanShare'] = False
  else:
    unknownArgumentExit()

def printDriveActivity(users):
  drive_ancestorId = u'root'
  drive_fileId = None
  todrive = False
  titles = [u'user.name', u'user.permissionId', u'target.id', u'target.name', u'target.mimeType']
  csvRows = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'fileid':
      drive_fileId = getString(OB_DRIVE_FILE_ID)
      drive_ancestorId = None
    elif myarg == u'folderid':
      drive_ancestorId = getString(OB_DRIVE_FOLDER_ID)
    elif myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  for user in users:
    user, activity = buildActivityGAPIObject(user)
    if not activity:
      continue
    page_message = u'Retrieved %%%%total_items%%%% activities for %s' % user
    feed = callGAPIpages(activity.activities(), u'list', u'activities',
                         page_message=page_message, source=u'drive.google.com', userId=u'me',
                         drive_ancestorId=drive_ancestorId, groupingStrategy=u'none',
                         drive_fileId=drive_fileId, pageSize=GC_Values[GC_ACTIVITY_MAX_RESULTS])
    while feed:
      addRowTitlesToCSVfile(flattenJSON(feed.popleft()[u'combinedEvent']), csvRows, titles)
  sortCSVTitles([u'user.name', u'user.permissionId', u'target.id', u'target.name', u'target.mimeType'], titles)
  writeCSVfile(csvRows, titles, u'Drive Activity', todrive)

def printDriveSettings(users):
  todrive = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  dont_show = [u'kind', u'selfLink', u'exportFormats', u'importFormats', u'maxUploadSizes', u'additionalRoleInfo', u'etag', u'features', u'user', u'isCurrentAppInstalled']
  csvRows = []
  titles = [u'email',]
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, drive = buildDriveGAPIObject(user)
    if not drive:
      continue
    sys.stderr.write(u'Getting Drive settings for %s%s' % (user, currentCountNL(i, count)))
    feed = callGAPI(drive.about(), u'get', soft_errors=True)
    if feed is None:
      continue
    row = {u'email': user}
    for setting in feed:
      if setting in dont_show:
        continue
      if setting == u'quotaBytesByService':
        for subsetting in feed[setting]:
          my_name = subsetting[u'serviceName']
          my_bytes = int(subsetting[u'bytesUsed'])
          row[my_name] = u'%smb' % (my_bytes / 1024 / 1024)
          if my_name not in titles:
            titles.append(my_name)
        continue
      row[setting] = feed[setting]
      if setting not in titles:
        titles.append(setting)
    csvRows.append(row)
  writeCSVfile(csvRows, titles, u'User Drive Settings', todrive)

def initFilePathInfo():
  return {u'ids': {}, u'allPaths': {}, u'localPaths': None}

def getFilePaths(drive, initialResult, filePathInfo):
  def _followParent(paths, parentId):
    try:
      paths.setdefault(parentId, {})
      result = callGAPI(drive.files(), u'get',
                        throw_reasons=GAPI_DRIVE_THROW_REASONS+[GAPI_FILE_NOT_FOUND],
                        fileId=parentId, fields=u'{0},parents(id)'.format(DRIVE_FILE_NAME))
      filePathInfo[u'ids'][parentId] = result[DRIVE_FILE_NAME]
      parents = result[u'parents']
      if parents:
        for lparent in parents:
          lparentId = lparent[u'id']
          if lparentId not in filePathInfo[u'allPaths']:
            _followParent(paths[parentId], lparentId)
            filePathInfo[u'allPaths'][lparentId] = paths[parentId][lparentId]
          else:
            paths[parentId][lparentId] = filePathInfo[u'allPaths'][lparentId]
    except (GAPI_fileNotFound, GAPI_serviceNotAvailable, GAPI_authError):
      pass

  def _makeFilePaths(localPaths, fplist, filePaths, name):
    for k, v in localPaths.items():
      fplist.append(filePathInfo[u'ids'][k])
      if not v:
        fp = fplist[:]
        fp.reverse()
        fp.append(name)
        filePaths.append(os.path.join(*fp))
        fplist.pop()
        return
      _makeFilePaths(v, fplist, filePaths, name)
      fplist.pop()
    return

  filePaths = []
  parents = initialResult[u'parents']
  if parents:
    filePathInfo[u'localPaths'] = {}
    for parent in parents:
      parentId = parent[u'id']
      if parentId not in filePathInfo[u'allPaths']:
        _followParent(filePathInfo[u'allPaths'], parentId)
      filePathInfo[u'localPaths'][parentId] = filePathInfo[u'allPaths'][parentId]
    fplist = []
    _makeFilePaths(filePathInfo[u'localPaths'], fplist, filePaths, initialResult[DRIVE_FILE_NAME])
  return ([u'Drive Folder', u'Drive File'][initialResult[u'mimeType'] != MIMETYPE_GA_FOLDER], filePaths)

DRIVEFILE_FIELDS_CHOICES_MAP = {
  u'alternatelink': DRIVE_FILE_VIEW_LINK,
  u'appdatacontents': u'appDataContents',
  u'cancomment': u'canComment',
  u'canreadrevisions': u'canReadRevisions',
  u'copyable': u'copyable',
  u'createddate': u'createdDate',
  u'createdtime': u'createdDate',
  u'description': u'description',
  u'editable': u'editable',
  u'explicitlytrashed': u'explicitlyTrashed',
  u'fileextension': u'fileExtension',
  u'filesize': u'fileSize',
  u'foldercolorrgb': u'folderColorRgb',
  u'fullfileextension': u'fullFileExtension',
  u'headrevisionid': u'headRevisionId',
  u'iconlink': u'iconLink',
  u'id': u'id',
  u'lastmodifyinguser': u'lastModifyingUser',
  u'lastmodifyingusername': u'lastModifyingUserName',
  u'lastviewedbyme': u'lastViewedByMeDate',
  u'lastviewedbymedate': u'lastViewedByMeDate',
  u'lastviewedbymetime': u'lastViewedByMeDate',
  u'lastviewedbyuser': u'lastViewedByMeDate',
  u'md5': u'md5Checksum',
  u'md5checksum': u'md5Checksum',
  u'md5sum': u'md5Checksum',
  u'mime': u'mimeType',
  u'mimetype': u'mimeType',
  u'modifiedbyme': u'modifiedByMeDate',
  u'modifiedbymedate': u'modifiedByMeDate',
  u'modifiedbymetime': u'modifiedByMeDate',
  u'modifiedbyuser': u'modifiedByMeDate',
  u'modifieddate': u'modifiedDate',
  u'modifiedtime': u'modifiedDate',
  u'name': DRIVE_FILE_NAME,
  u'originalfilename': u'originalFilename',
  u'ownedbyme': u'ownedByMe',
  u'ownernames': u'ownerNames',
  u'owners': u'owners',
  u'parents': u'parents',
  u'permissions': u'permissions',
  u'quotabytesused': u'quotaBytesUsed',
  u'quotaused': u'quotaBytesUsed',
  u'shareable': u'shareable',
  u'shared': u'shared',
  u'sharedwithmedate': u'sharedWithMeDate',
  u'sharedwithmetime': u'sharedWithMeDate',
  u'sharinguser': u'sharingUser',
  u'spaces': u'spaces',
  u'thumbnaillink': u'thumbnailLink',
  u'title': DRIVE_FILE_NAME,
  u'userpermission': u'userPermission',
  u'version': u'version',
  u'viewedbyme': u'labels(viewed)',
  u'viewedbymedate': u'lastViewedByMeDate',
  u'viewedbymetime': u'lastViewedByMeDate',
  u'viewerscancopycontent': u'labels(restricted)',
  u'webcontentlink': u'webContentLink',
  u'webviewlink': u'webViewLink',
  u'writerscanshare': u'writersCanShare',
  }

FILEINFO_FIELDS_TITLES = [DRIVE_FILE_NAME, u'mimeType']
FILEPATH_TITLES = [DRIVE_FILE_NAME, u'id', u'mimeType', u'parents']
FILEPATH_FIELDS = [DRIVE_FILE_NAME, u'id', u'mimeType', u'parents(id)']

def showDriveFileInfo(users):
  def _setSelectionFields():
    skip_objects.extend([field for field in FILEINFO_FIELDS_TITLES if field not in fieldsList])
    fieldsList.extend(FILEINFO_FIELDS_TITLES)
    if filepath:
      skip_objects.extend([field for field in FILEPATH_TITLES if field not in fieldsList])
      fieldsList.extend(FILEPATH_FIELDS)

  filepath = False
  fieldsList = []
  labelsList = []
  skip_objects = []
  fileIdSelection = getDriveFileEntity()
  body, parameters = initializeDriveFileAttributes()
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'filepath':
      filepath = True
    elif myarg == u'allfields':
      fieldsList = []
    elif myarg in DRIVEFILE_FIELDS_CHOICES_MAP:
      fieldsList.append(DRIVEFILE_FIELDS_CHOICES_MAP[myarg])
    elif myarg in DRIVEFILE_LABEL_CHOICES_MAP:
      labelsList.append(DRIVEFILE_LABEL_CHOICES_MAP[myarg])
    else:
      unknownArgumentExit()
  if fieldsList or labelsList:
    _setSelectionFields()
    fields = u','.join(set(fieldsList))
    if labelsList:
      fields += u',labels({0})'.format(u','.join(set(labelsList)))
  else:
    fields = u'*'
    skip_objects.extend([u'kind', u'etag'])
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, drive, jcount = validateUserGetFileIDs(user, i, count, fileIdSelection, body, parameters)
    if not drive:
      continue
    if jcount == 0:
      print u'User: {0}, No Drive Files/Folders{1}'.format(user, currentCount(i, count))
      continue
    if filepath:
      filePathInfo = initFilePathInfo()
    print u'User: {0}, Drive Files/Folders:{1}'.format(user, currentCount(i, count))
    j = 0
    for fileId in fileIdSelection[u'fileIds']:
      j += 1
      try:
        result = callGAPI(drive.files(), u'get',
                          throw_reasons=GAPI_DRIVE_THROW_REASONS+[GAPI_FILE_NOT_FOUND],
                          fileId=fileId, fields=fields)
        print u'  {0}: {1}{2}'.format([u'Drive Folder', u'Drive File'][result[u'mimeType'] != MIMETYPE_GA_FOLDER], u'{0} ({1})'.format(result[DRIVE_FILE_NAME], fileId), currentCount(j, jcount))
        if filepath:
          _, paths = getFilePaths(drive, result, filePathInfo)
          kcount = len(paths)
          printKeyValueList(u'    ', [u'paths', kcount])
          for path in paths:
            printKeyValueList(u'      ', [u'path', path])
        showJSON(None, result, skip_objects, spacing=u'    ')
      except GAPI_fileNotFound:
        sys.stderr.write(u'User: {0}, {1}: {2}, Does not exist{3}'.format(user, u'Drive File/Folder ID', fileId, currentCountNL(j, jcount)))
      except (GAPI_serviceNotAvailable, GAPI_authError):
        entityServiceNotApplicableWarning(u'User', user, i, count)
        break

def showDriveFileRevisions(users):
  fileIdSelection = getDriveFileEntity()
  body, parameters = initializeDriveFileAttributes()
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, drive, jcount = validateUserGetFileIDs(user, i, count, fileIdSelection, body, parameters)
    if not drive:
      continue
    if jcount == 0:
      print u'User: {0}, No Drive Files/Folders{1}'.format(user, currentCount(i, count))
      continue
    print u'User: {0}, Drive Files/Folders:{1}'.format(user, currentCount(i, count))
    j = 0
    for fileId in fileIdSelection[u'fileIds']:
      j += 1
      try:
        result = callGAPI(drive.revisions(), u'list',
                          throw_reasons=GAPI_DRIVE_THROW_REASONS+[GAPI_FILE_NOT_FOUND, GAPI_BAD_REQUEST],
                          fileId=fileId, fields=DRIVE_REVISIONS_LIST)
        print u'{0}: {1}{2}'.format(u'Drive File ID', fileId, currentCount(j, jcount))
        for revision in result[DRIVE_REVISIONS_LIST]:
          print u'  Revision ID: {0}'.format(revision[u'id'])
          showJSON(None, revision, [u'id',], spacing=u'  ')
      except GAPI_fileNotFound:
        sys.stderr.write(u'User: {0}, {1}: {2}, Does not exist{3}'.format(user, u'Drive File/Folder ID', fileId, currentCountNL(j, jcount)))
      except GAPI_badRequest as e:
        sys.stderr.write(u'User: {0}, {1}: {2}, {3}{4}'.format(user, u'Drive File/Folder ID', fileId, e.message, currentCountNL(j, jcount)))
      except (GAPI_serviceNotAvailable, GAPI_authError):
        entityServiceNotApplicableWarning(u'User', user, i, count)
        break

def _stripMeInOwners(query):
  if not query:
    return query
  if query == ME_IN_OWNERS:
    return None
  if query.startswith(ME_IN_OWNERS_AND):
    return query[len(ME_IN_OWNERS_AND):]
  return query

DRIVEFILE_ORDERBY_CHOICES_MAP = {
  u'createddate': u'createdDate',
  u'createdtime': u'createdDate',
  u'folder': u'folder',
  u'lastviewedbyme': u'lastViewedByMeDate',
  u'lastviewedbymedate': u'lastViewedByMeDate',
  u'lastviewedbymetime': u'lastViewedByMeDate',
  u'lastviewedbyuser': u'lastViewedByMeDate',
  u'modifiedbyme': u'modifiedByMeDate',
  u'modifiedbymedate': u'modifiedByMeDate',
  u'modifiedbymetime': u'modifiedByMeDate',
  u'modifiedbyuser': u'modifiedByMeDate',
  u'modifieddate': u'modifiedDate',
  u'modifiedtime': u'modifiedDate',
  u'name': DRIVE_FILE_NAME,
  u'quotabytesused': u'quotaBytesUsed',
  u'quotaused': u'quotaBytesUsed',
  u'recency': u'recency',
  u'sharedwithmedate': u'sharedWithMeDate',
  u'sharedwithmetime': u'sharedWithMeDate',
  u'starred': u'starred',
  u'title': DRIVE_FILE_NAME,
  u'viewedbymedate': u'lastViewedByMeDate',
  u'viewedbymetime': u'lastViewedByMeDate',
  }

FILELIST_TITLES = [u'id', u'mimeType', u'parents']
FILELIST_FIELDS = [u'id', u'mimeType', u'parents(id)']

def printDriveFileList(users):
  def _setSelectionFields():
    if fileIdSelection:
      skip_objects.extend([field for field in FILELIST_TITLES if field not in fieldsList])
      fieldsList.extend(FILELIST_FIELDS)
    if filepath:
      skip_objects.extend([field for field in FILEPATH_TITLES if field not in fieldsList])
      fieldsList.extend(FILEPATH_FIELDS)

  def _printFileInfo(f_file):
    if f_file.get(u'printed'):
      return
    f_file[u'printed'] = True
    row = {u'Owner': user}
    if filepath:
      _, paths = getFilePaths(drive, f_file, filePathInfo)
      kcount = len(paths)
      row[u'paths'] = kcount
      k = 0
      for path in paths:
        key = u'path.{0}'.format(k)
        if key not in titles:
          titles.append(key)
        row[key] = path
        k += 1
    for attrib in f_file:
      if attrib in skip_objects:
        continue
      if not isinstance(f_file[attrib], dict):
        if isinstance(f_file[attrib], list):
          if f_file[attrib]:
            if attrib not in titles:
              titles.append(attrib)
            if isinstance(f_file[attrib][0], (str, unicode, int, bool)):
              row[attrib] = delimiter.join(f_file[attrib])
            else:
              row[attrib] = len(f_file[attrib])
              for j, l_attrib in enumerate(f_file[attrib]):
                for list_attrib in l_attrib:
                  if list_attrib in [u'kind', u'etag', u'selfLink']:
                    continue
                  x_attrib = u'{0}.{1}.{2}'.format(attrib, j, list_attrib)
                  row[x_attrib] = l_attrib[list_attrib]
                  if x_attrib not in titles:
                    titles.append(x_attrib)
        elif isinstance(f_file[attrib], (str, unicode, int, bool)):
          row[attrib] = f_file[attrib]
          if attrib not in titles:
            titles.append(attrib)
        else:
          sys.stderr.write(u'Drive File ID: {0}, Attribute: {1}, Unknown type: {2}\n'.format(f_file[u'id'], attrib, type(f_file[attrib])))
      elif attrib == u'labels':
        for dict_attrib in f_file[attrib]:
          row[dict_attrib] = f_file[attrib][dict_attrib]
          if dict_attrib not in titles:
            titles.append(dict_attrib)
      else:
        for dict_attrib in f_file[attrib]:
          if dict_attrib in [u'kind', u'etag']:
            continue
          x_attrib = u'{0}.{1}'.format(attrib, dict_attrib)
          row[x_attrib] = f_file[attrib][dict_attrib]
          if x_attrib not in titles:
            titles.append(x_attrib)
    csvRows.append(row)

  def _printDriveFolderContents(folderId, depth):
    for f_file in feed:
      for parent in f_file.get(u'parents', []):
        if folderId == parent[u'id']:
          _printFileInfo(f_file)
          if f_file[u'mimeType'] == MIMETYPE_GA_FOLDER and (maxdepth == -1 or depth < maxdepth):
            _printDriveFolderContents(f_file[u'id'], depth+1)
          break

  allfields = anyowner = filepath = todrive = False
  maxdepth = -1
  fieldsList = []
  fieldsTitles = {}
  labelsList = []
  orderByList = []
  skip_objects = [u'printed',]
  titles = [u'Owner',]
  csvRows = []
  query = ME_IN_OWNERS
  fileIdSelection = None
  body, parameters = initializeDriveFileAttributes()
  delimiter = GC_Values[GC_CSV_OUTPUT_FIELD_DELIMITER]
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'todrive':
      todrive = True
    elif myarg == u'filepath':
      filepath = True
    elif myarg == u'orderby':
      fieldName = getChoice(DRIVEFILE_ORDERBY_CHOICES_MAP, mapChoice=True)
      if getChoice(SORTORDER_CHOICES_MAP, defaultChoice=None, mapChoice=True) != u'DESCENDING':
        orderByList.append(fieldName)
      else:
        orderByList.append(u'{0} desc'.format(fieldName))
    elif myarg == u'query':
      query += u' and '+getString(OB_QUERY)
    elif myarg == u'fullquery':
      query = getString(OB_QUERY)
    elif myarg == u'anyowner':
      anyowner = True
    elif myarg == u'select':
      fileIdSelection = getDriveFileEntity()
    elif myarg == u'depth':
      maxdepth = getInteger(minVal=-1)
    elif myarg == u'allfields':
      fieldsList = []
      allfields = True
    elif myarg in DRIVEFILE_FIELDS_CHOICES_MAP:
      addFieldToCSVfile(myarg, {myarg: [DRIVEFILE_FIELDS_CHOICES_MAP[myarg]]}, fieldsList, fieldsTitles, titles)
    elif myarg in DRIVEFILE_LABEL_CHOICES_MAP:
      addFieldToCSVfile(myarg, {myarg: [DRIVEFILE_LABEL_CHOICES_MAP[myarg]]}, labelsList, fieldsTitles, titles)
    elif myarg == u'delimiter':
      delimiter = getString(OB_STRING, minLen=1, maxLen=1)
    else:
      unknownArgumentExit()
  if fieldsList or labelsList:
    _setSelectionFields()
    fields = u'nextPageToken,{0}('.format(DRIVE_FILES_LIST)
    if fieldsList:
      fields += u','.join(set(fieldsList))
      if labelsList:
        fields += u','
    if labelsList:
      fields += u'labels({0})'.format(u','.join(set(labelsList)))
    fields += u')'
  elif not allfields:
    for field in [u'name', DRIVE_FILE_VIEW_LINK]:
      addFieldToCSVfile(field, {field: [DRIVEFILE_FIELDS_CHOICES_MAP[field.lower()]]}, fieldsList, fieldsTitles, titles)
    _setSelectionFields()
    fields = u'nextPageToken,{0}({1})'.format(DRIVE_FILES_LIST, u','.join(set(fieldsList)))
  else:
    fields = u'*'
    skip_objects.extend([u'kind', u'etag'])
  if orderByList:
    orderBy = u','.join(orderByList)
  else:
    orderBy = None
  if anyowner:
    query = _stripMeInOwners(query)
    if fileIdSelection:
      fileIdSelection[u'query'] = _stripMeInOwners(fileIdSelection[u'query'])
  if filepath:
    addTitlesToCSVfile([u'paths',], titles)
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, drive = buildDriveGAPIObject(user)
    if not drive:
      continue
    if filepath:
      filePathInfo = initFilePathInfo()
    try:
      sys.stderr.write(u'Getting all files for %s%s' % (user, currentCountNL(i, count)))
      page_message = u' got %%%%total_items%%%% files for %s...\n' % user
      feed = callGAPIpages(drive.files(), u'list', DRIVE_FILES_LIST,
                           page_message=page_message,
                           throw_reasons=GAPI_DRIVE_THROW_REASONS+[GAPI_INVALID_QUERY, GAPI_FILE_NOT_FOUND],
                           q=query, orderBy=orderBy, fields=fields, maxResults=GC_Values[GC_DRIVE_MAX_RESULTS])
      if fileIdSelection is None:
        while feed:
          _printFileInfo(feed.popleft())
      else:
        user, drive, _ = validateUserGetFileIDs(user, i, count, fileIdSelection, body, parameters, drive=drive)
        for fileId in fileIdSelection[u'fileIds']:
          _printDriveFolderContents(fileId, 0)
    except GAPI_invalidQuery:
      sys.stderr.write(u'User: {0}, Show Failed: Query ({1}) Invalid{2}'.format(user, query, currentCountNL(i, count)))
      break
    except GAPI_fileNotFound:
      sys.stderr.write(u' got 0 files for %s...\n' % user)
    except (GAPI_serviceNotAvailable, GAPI_authError):
      entityServiceNotApplicableWarning(u'User', user, i, count)
  if allfields:
    sortCSVTitles([u'Owner', u'id', DRIVE_FILE_NAME], titles)
  writeCSVfile(csvRows, titles, u'%s %s Drive Files' % (CL_argv[1], CL_argv[2]), todrive)

def showDriveFilePath(users):
  fileIdSelection = getDriveFileEntity()
  checkForExtraneousArguments()
  body, parameters = initializeDriveFileAttributes()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, drive, jcount = validateUserGetFileIDs(user, i, count, fileIdSelection, body, parameters)
    if not drive:
      continue
    if jcount == 0:
      print u'No files to show for %s' % user
      continue
    filePathInfo = initFilePathInfo()
    j = 0
    for fileId in fileIdSelection[u'fileIds']:
      j += 1
      try:
        result = callGAPI(drive.files(), u'get',
                          throw_reasons=GAPI_DRIVE_THROW_REASONS+[GAPI_FILE_NOT_FOUND],
                          fileId=fileId, fields=u'{0},mimeType,parents(id)'.format(DRIVE_FILE_NAME))
        entityType, paths = getFilePaths(drive, result, filePathInfo)
        kcount = len(paths)
        print u'{0}: {1}, {2}{3}'.format(entityType, u'{0} ({1})'.format(result[DRIVE_FILE_NAME], fileId), u'Show {0} Drive Paths'.format(kcount), currentCount(j, jcount))
        k = 0
        for path in paths:
          k += 1
          print u'  Drive Path: {0}{1}'.format(path, currentCount(k, kcount))
      except GAPI_fileNotFound:
        print u'User: {0}, Drive File/Folder ID: {1}, Does not exist'.format(user, fileId)
      except (GAPI_serviceNotAvailable, GAPI_authError):
        entityServiceNotApplicableWarning(u'User', user, i, count)
        break

def showDriveFileTree(users):
  def _printDriveFolderContents(feed, folderId, depth):
    for f_file in feed:
      for parent in f_file[u'parents']:
        if folderId == parent[u'id']:
          print convertUTF8(u'  '*(depth+1)+f_file[DRIVE_FILE_NAME])
          if f_file[u'mimeType'] == MIMETYPE_GA_FOLDER and (maxdepth == -1 or depth < maxdepth):
            _printDriveFolderContents(feed, f_file[u'id'], depth+1)
          break

  anyowner = False
  maxdepth = -1
  query = ME_IN_OWNERS
  fileIdSelection = None
  body, parameters = initializeDriveFileAttributes()
  orderByList = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'anyowner':
      anyowner = True
    elif myarg == u'select':
      fileIdSelection = getDriveFileEntity()
    elif myarg == u'depth':
      maxdepth = getInteger(minVal=-1)
    elif myarg == u'orderby':
      fieldName = getChoice(DRIVEFILE_ORDERBY_CHOICES_MAP, mapChoice=True)
      if getChoice(SORTORDER_CHOICES_MAP, defaultChoice=None, mapChoice=True) != u'DESCENDING':
        orderByList.append(fieldName)
      else:
        orderByList.append(u'{0} desc'.format(fieldName))
    else:
      unknownArgumentExit()
  if not fileIdSelection:
    fileIdSelection = initDriveFileEntity()
    cleanFileIDsList(fileIdSelection, [u'root',])
  if orderByList:
    orderBy = u','.join(orderByList)
  else:
    orderBy = None
  if anyowner:
    query = _stripMeInOwners(query)
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, drive, jcount = validateUserGetFileIDs(user, i, count, fileIdSelection, body, parameters)
    if not drive:
      continue
    if jcount == 0:
      print u'No files to show for %s' % (user)
      continue
    try:
      sys.stderr.write(u'Getting all files for %s%s' % (user, currentCountNL(i, count)))
      page_message = u' got %%%%total_items%%%% files for %s...\n' % user
      feed = callGAPIpages(drive.files(), u'list', DRIVE_FILES_LIST,
                           page_message=page_message,
                           throw_reasons=GAPI_DRIVE_THROW_REASONS,
                           q=query, orderBy=orderBy, fields=u'nextPageToken,{0}(id,{1},mimeType,parents(id))'.format(DRIVE_FILES_LIST, DRIVE_FILE_NAME), maxResults=GC_Values[GC_DRIVE_MAX_RESULTS])
      j = 0
      for fileId in fileIdSelection[u'fileIds']:
        j += 1
        try:
          result = callGAPI(drive.files(), u'get',
                            throw_reasons=GAPI_DRIVE_THROW_REASONS+[GAPI_FILE_NOT_FOUND],
                            fileId=fileId, fields=DRIVE_FILE_NAME)
          print u'{0}: {1}{2}'.format(u'Drive File/Folder', result[DRIVE_FILE_NAME], currentCount(j, jcount))
          _printDriveFolderContents(feed, fileId, 0)
        except GAPI_fileNotFound:
          print u'User: {0}, {1}: {2}, Does not exist{3}'.format(user, u'Drive File/Folder ID', fileId, currentCount(j, jcount))
        except (GAPI_serviceNotAvailable, GAPI_authError):
          entityServiceNotApplicableWarning(u'User', user, i, count)
          break
    except (GAPI_serviceNotAvailable, GAPI_authError):
      entityServiceNotApplicableWarning(u'User', user, i, count)

def addDriveFile(users):
  media_body = None
  body, parameters = initializeDriveFileAttributes()
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'drivefilename':
      body[DRIVE_FILE_NAME] = getString(OB_DRIVE_FOLDER_NAME)
    else:
      getDriveFileAttribute(body, parameters, myarg, False)
  for user in users:
    user, drive = buildDriveGAPIObject(user)
    if not drive:
      continue
    if parameters[DFA_PARENTQUERY]:
      more_parents = doDriveSearch(drive, query=parameters[DFA_PARENTQUERY])
      body.setdefault(u'parents', [])
      for a_parent in more_parents:
        body[u'parents'].append({u'id': a_parent})
    if parameters[DFA_LOCALFILEPATH]:
      try:
        media_body = googleapiclient.http.MediaFileUpload(parameters[DFA_LOCALFILEPATH], mimetype=parameters[DFA_LOCALMIMETYPE], resumable=True)
      except IOError as e:
        systemErrorExit(FILE_ERROR_RC, e)
    result = callGAPI(drive.files(), DRIVE_CREATE_FILE,
                      convert=parameters[DFA_CONVERT], ocr=parameters[DFA_OCR], ocrLanguage=parameters[DFA_OCRLANGUAGE], media_body=media_body, body=body, fields=u'id')
    if parameters[DFA_LOCALFILENAME]:
      print u'Successfully uploaded %s to Drive file ID %s' % (parameters[DFA_LOCALFILENAME], result[u'id'])
    else:
      print u'Successfully created drive file/folder ID %s' % (result[u'id'])

def doUpdateDriveFile(users):
  media_body = None
  operation = u'update'
  fileIdSelection = getDriveFileEntity()
  body, parameters = initializeDriveFileAttributes()
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'copy':
      operation = u'copy'
    elif myarg == u'newfilename':
      body[DRIVE_FILE_NAME] = getString(OB_DRIVE_FILE_NAME)
    else:
      getDriveFileAttribute(body, parameters, myarg, True)
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, drive, jcount = validateUserGetFileIDs(user, i, count, fileIdSelection, body, parameters)
    if not drive:
      continue
    if jcount == 0:
      print u'No files to %s for %s' % (operation, user)
      continue
    if operation == u'update':
      if parameters[DFA_LOCALFILEPATH]:
        try:
          media_body = googleapiclient.http.MediaFileUpload(parameters[DFA_LOCALFILEPATH], mimetype=parameters[DFA_LOCALMIMETYPE], resumable=True)
        except IOError as e:
          systemErrorExit(FILE_ERROR_RC, e)
      for fileId in fileIdSelection[u'fileIds']:
        if media_body:
          result = callGAPI(drive.files(), DRIVE_UPDATE_FILE,
                            fileId=fileId, ocr=parameters[DFA_OCR], ocrLanguage=parameters[DFA_OCRLANGUAGE],
                            addParents=u','.join(parameters[DFA_ADD_PARENTS]), removeParents=u','.join(parameters[DFA_REMOVE_PARENTS]),
                            media_body=media_body, body=body, fields=u'id')
          print u'Successfully updated %s drive file with content from %s' % (result[u'id'], parameters[DFA_LOCALFILENAME])
        else:
          result = callGAPI(drive.files(), DRIVE_PATCH_FILE,
                            fileId=fileId, ocr=parameters[DFA_OCR], ocrLanguage=parameters[DFA_OCRLANGUAGE],
                            addParents=u','.join(parameters[DFA_ADD_PARENTS]), removeParents=u','.join(parameters[DFA_REMOVE_PARENTS]),
                            body=body, fields=u'id')
          print u'Successfully updated drive file/folder ID %s' % (result[u'id'])
    else:
      for fileId in fileIdSelection[u'fileIds']:
        result = callGAPI(drive.files(), u'copy',
                          fileId=fileId, convert=parameters[DFA_CONVERT], ocr=parameters[DFA_OCR], ocrLanguage=parameters[DFA_OCRLANGUAGE], body=body, fields=u'id')
        print u'Successfully copied %s to %s' % (fileId, result[u'id'])

DELETE_DRIVEFILE_FUNCTION_TO_ACTION_MAP = {u'delete': u'purging', u'trash': u'trashing', u'untrash': u'untrashing',}

def deleteDriveFile(users):
  fileIdSelection = getDriveFileEntity()
  body, parameters = initializeDriveFileAttributes()
  function = u'trash'
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'purge':
      function = u'delete'
    elif myarg == u'untrash':
      function = u'untrash'
    else:
      unknownArgumentExit()
  action = DELETE_DRIVEFILE_FUNCTION_TO_ACTION_MAP[function]
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, drive, jcount = validateUserGetFileIDs(user, i, count, fileIdSelection, body, parameters)
    if not drive:
      continue
    if jcount == 0:
      print u'No files to %s for %s' % (function, user)
      continue
    j = 0
    for fileId in fileIdSelection[u'fileIds']:
      j += 1
      print u'%s %s for %s%s' % (action, fileId, user, currentCount(j, jcount))
      callGAPI(drive.files(), function, fileId=fileId)

DOCUMENT_FORMATS_MAP = {
  u'csv': [{u'mime': u'text/csv', u'ext': u'.csv'}],
  u'html': [{u'mime': u'text/html', u'ext': u'.html'}],
  u'txt': [{u'mime': u'text/plain', u'ext': u'.txt'}],
  u'tsv': [{u'mime': u'text/tsv', u'ext': u'.tsv'}],
  u'jpeg': [{u'mime': u'image/jpeg', u'ext': u'.jpeg'}],
  u'jpg': [{u'mime': u'image/jpeg', u'ext': u'.jpg'}],
  u'png': [{u'mime': u'image/png', u'ext': u'.png'}],
  u'svg': [{u'mime': u'image/svg+xml', u'ext': u'.svg'}],
  u'pdf': [{u'mime': u'application/pdf', u'ext': u'.pdf'}],
  u'rtf': [{u'mime': u'application/rtf', u'ext': u'.rtf'}],
  u'zip': [{u'mime': u'application/zip', u'ext': u'.zip'}],
  u'pptx': [{u'mime': u'application/vnd.openxmlformats-officedocument.presentationml.presentation', u'ext': u'.pptx'}],
  u'xlsx': [{u'mime': u'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet', u'ext': u'.xlsx'}],
  u'docx': [{u'mime': u'application/vnd.openxmlformats-officedocument.wordprocessingml.document', u'ext': u'.docx'}],
  u'ms': [{u'mime': u'application/vnd.openxmlformats-officedocument.presentationml.presentation', u'ext': u'.pptx'},
          {u'mime': u'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet', u'ext': u'.xlsx'},
          {u'mime': u'application/vnd.openxmlformats-officedocument.wordprocessingml.document', u'ext': u'.docx'}],
  u'microsoft': [{u'mime': u'application/vnd.openxmlformats-officedocument.presentationml.presentation', u'ext': u'.pptx'},
                 {u'mime': u'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet', u'ext': u'.xlsx'},
                 {u'mime': u'application/vnd.openxmlformats-officedocument.wordprocessingml.document', u'ext': u'.docx'}],
  u'micro$oft': [{u'mime': u'application/vnd.openxmlformats-officedocument.presentationml.presentation', u'ext': u'.pptx'},
                 {u'mime': u'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet', u'ext': u'.xlsx'},
                 {u'mime': u'application/vnd.openxmlformats-officedocument.wordprocessingml.document', u'ext': u'.docx'}],
  u'odt': [{u'mime': u'application/vnd.oasis.opendocument.text', u'ext': u'.odt'}],
  u'ods': [{u'mime': u'application/x-vnd.oasis.opendocument.spreadsheet', u'ext': u'.ods'}],
  u'openoffice': [{u'mime': u'application/vnd.oasis.opendocument.text', u'ext': u'.odt'},
                  {u'mime': u'application/x-vnd.oasis.opendocument.spreadsheet', u'ext': u'.ods'}],
  }

def getDriveFile(users):
  fileIdSelection = getDriveFileEntity()
  body, parameters = initializeDriveFileAttributes()
  revisionId = None
  exportFormatName = u'openoffice'
  exportFormats = DOCUMENT_FORMATS_MAP[exportFormatName]
  targetFolder = GC_Values[GC_DRIVE_DIR]
  safe_filename_chars = "-_.() %s%s" % (string.ascii_letters, string.digits)
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'format':
      exportFormatChoices = getString(OB_FORMAT_LIST).replace(u',', u' ').lower().split()
      exportFormats = []
      for exportFormat in exportFormatChoices:
        if exportFormat in DOCUMENT_FORMATS_MAP:
          exportFormats.extend(DOCUMENT_FORMATS_MAP[exportFormat])
        else:
          putArgumentBack()
          invalidChoiceExit(DOCUMENT_FORMATS_MAP)
    elif myarg == u'targetfolder':
      targetFolder = os.path.expanduser(getString(OB_FILE_PATH))
      if not os.path.isdir(targetFolder):
        os.makedirs(targetFolder)
    elif myarg == u'revision':
      revisionId = getInteger(minVal=1)
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, drive, jcount = validateUserGetFileIDs(user, i, count, fileIdSelection, body, parameters)
    if not drive:
      continue
    if jcount == 0:
      print u'No files to download for %s' % user
    for fileId in fileIdSelection[u'fileIds']:
      extension = None
      result = callGAPI(drive.files(), u'get',
                        fileId=fileId, fields=u'{0},mimeType,fileSize,downloadUrl,exportLinks'.format(DRIVE_FILE_NAME))
      if result[u'mimeType'] == MIMETYPE_GA_FOLDER:
        print convertUTF8(u'Skipping download of folder %s' % result[DRIVE_FILE_NAME])
        continue
      if u'fileSize' in result:
        my_line = u'Downloading: %%s of %s bytes' % formatFileSize(int(result[u'fileSize']))
      else:
        my_line = u'Downloading Google Doc: %s'
      if u'downloadUrl' in result:
        download_url = result[u'downloadUrl']
      elif u'exportLinks' in result:
        for exportFormat in exportFormats:
          if exportFormat[u'mime'] in result[u'exportLinks']:
            download_url = result[u'exportLinks'][exportFormat[u'mime']]
            extension = exportFormat[u'ext']
            break
        else:
          print convertUTF8(u'Skipping download of file {0}, Format {1} not available'.format(result[DRIVE_FILE_NAME], u','.join(exportFormatChoices)))
          continue
      else:
        print convertUTF8(u'Skipping download of file {0}, Format not downloadable')
        continue
      file_title = result[DRIVE_FILE_NAME]
      safe_file_title = u''.join(c for c in file_title if c in safe_filename_chars)
      filename = os.path.join(targetFolder, safe_file_title)
      y = 0
      while True:
        if extension and filename.lower()[-len(extension):] != extension:
          filename += extension
        if not os.path.isfile(filename):
          break
        y += 1
        filename = os.path.join(targetFolder, u'({0})-{1}'.format(y, safe_file_title))
      print convertUTF8(my_line % filename)
      if revisionId:
        download_url = u'{0}&revision={1}'.format(download_url, revisionId)
      _, content = drive._http.request(download_url)
      writeFile(filename, content, continueOnError=True)

def transferDriveFiles(users):
  target_user = getEmailAddress()
  remove_source_user = True
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'keepuser':
      remove_source_user = False
    else:
      unknownArgumentExit()
  source_query = ME_IN_OWNERS_AND+u"trashed = false"
  target_query = ME_IN_OWNERS_AND+u"mimeType = '{0}'".format(MIMETYPE_GA_FOLDER)
  target_user, target_drive = buildDriveGAPIObject(target_user)
  if not target_drive:
    return
  target_about = callGAPI(target_drive.about(), u'get', fields=u'quotaBytesTotal,quotaBytesUsed')
  target_drive_free = int(target_about[u'quotaBytesTotal']) - int(target_about[u'quotaBytesUsed'])
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, source_drive = buildDriveGAPIObject(user)
    if not source_drive:
      continue
    source_about = callGAPI(source_drive.about(), u'get', fields=u'quotaBytesTotal,quotaBytesUsed,rootFolderId,permissionId')
    source_drive_size = int(source_about[u'quotaBytesUsed'])
    if target_drive_free < source_drive_size:
      systemErrorExit(4, MESSAGE_NO_TRANSFER_LACK_OF_DISK_SPACE.format(source_drive_size / 1024 / 1024, target_drive_free / 1024 / 1024))
    print u'Source drive size: %smb  Target drive free: %smb' % (source_drive_size / 1024 / 1024, target_drive_free / 1024 / 1024)
    target_drive_free = target_drive_free - source_drive_size # prep target_drive_free for next user
    source_root = source_about[u'rootFolderId']
    source_permissionid = source_about[u'permissionId']
    sys.stderr.write(u"Getting file list for source user: %s%s" % (user, currentCountNL(i, count)))
    page_message = u'  got %%total_items%% files\n'
    source_drive_files = callGAPIpages(source_drive.files(), u'list', DRIVE_FILES_LIST, page_message=page_message,
                                       q=source_query, fields=u'nextPageToken,{0}(id,parents,mimeType)'.format(DRIVE_FILES_LIST))
    all_source_file_ids = [source_drive_file[u'id'] for source_drive_file in source_drive_files]
    sys.stderr.write(u"Getting folder list for target user: %s...\n" % (target_user))
    page_message = u'  got %%total_items%% folders\n'
    target_folders = callGAPIpages(target_drive.files(), u'list', DRIVE_FILES_LIST, page_message=page_message,
                                   q=target_query, fields=u'nextPageToken,{0}(id,{1})'.format(DRIVE_FILES_LIST, DRIVE_FILE_NAME))
    got_top_folder = False
    all_target_folder_ids = []
    for target_folder in target_folders:
      all_target_folder_ids.append(target_folder[u'id'])
      if (not got_top_folder) and target_folder[DRIVE_FILE_NAME] == u'%s old files' % user:
        target_top_folder = target_folder[u'id']
        got_top_folder = True
    if not got_top_folder:
      create_folder = callGAPI(target_drive.files(), DRIVE_CREATE_FILE,
                               body={DRIVE_FILE_NAME: u'%s old files' % user, u'mimeType': u'application/vnd.google-apps.folder'}, fields=u'id')
      target_top_folder = create_folder[u'id']
    transferred_files = []
    j = 0
    jcount = len(source_drive_files)
    while True: # we loop thru, skipping files until all of their parents are done
      skipped_files = False
      for drive_file in source_drive_files:
        file_id = drive_file[u'id']
        if file_id in transferred_files:
          continue
        source_parents = drive_file[u'parents']
        skip_file_for_now = False
        for source_parent in source_parents:
          if source_parent[u'id'] not in all_source_file_ids and source_parent[u'id'] not in all_target_folder_ids:
            continue  # means this parent isn't owned by source or target, shouldn't matter
          if source_parent[u'id'] not in transferred_files and source_parent[u'id'] != source_root:
            #print u'skipping %s' % file_id
            skipped_files = skip_file_for_now = True
            break
        if skip_file_for_now:
          continue
        transferred_files.append(drive_file[u'id'])
        j += 1
        print u'Changing owner for file %s%s' % (drive_file[u'id'], currentCount(j, jcount))
        body = {u'role': u'owner', u'type': u'user', u'value': target_user}
        callGAPI(source_drive.permissions(), DRIVE_CREATE_PERMISSIONS,
                 soft_errors=True, fileId=file_id, sendNotificationEmails=False, body=body)
        target_parents = []
        for parent in source_parents:
          try:
            if parent[u'isRoot']:
              target_parents.append({u'id': target_top_folder})
            else:
              target_parents.append({u'id': parent[u'id']})
          except TypeError:
            pass
        callGAPI(target_drive.files(), DRIVE_PATCH_FILE, soft_errors=True, retry_reasons=[u'notFound'], fileId=file_id, body={u'parents': target_parents})
        if remove_source_user:
          callGAPI(target_drive.permissions(), u'delete', soft_errors=True, fileId=file_id, permissionId=source_permissionid)
      if not skipped_files:
        break

def validateUserGetPermissionId(user):
  _, drive = buildDriveGAPIObject(user)
  if drive:
    try:
      result = callGAPI(drive.about(), u'get',
                        throw_reasons=GAPI_DRIVE_THROW_REASONS,
                        fields=u'user(permissionId)')
      return result[u'user'][u'permissionId']
    except (GAPI_serviceNotAvailable, GAPI_authError):
      entityServiceNotApplicableWarning(u'User', user, 0, 0)
  return None

def deleteEmptyDriveFolders(users):
  checkForExtraneousArguments()
  query = ME_IN_OWNERS_AND+u"mimeType = '{0}'".format(MIMETYPE_GA_FOLDER)
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, drive = buildDriveGAPIObject(user)
    if not drive:
      continue
    deleted_empty = True
    while deleted_empty:
      sys.stderr.write(u'Getting all folders for %s%s' % (user, currentCountNL(i, count)))
      page_message = u' got %%%%total_items%%%% folders for %s...\n' % user
      feed = callGAPIpages(drive.files(), u'list', DRIVE_FILES_LIST,
                           page_message=page_message,
                           q=query, fields=u'nextPageToken,{0}(id,{1})'.format(DRIVE_FILES_LIST, DRIVE_FILE_NAME), maxResults=GC_Values[GC_DRIVE_MAX_RESULTS])
      deleted_empty = False
      for folder in feed:
        children = callGAPI(drive.children(), u'list',
                            folderId=folder[u'id'], fields=u'{0}(id)'.format(DRIVE_FILES_LIST), maxResults=1)
        if (not children) or (DRIVE_FILES_LIST not in children) or (len(children[DRIVE_FILES_LIST]) == 0):
          print convertUTF8(u' deleting empty folder %s...' % folder[DRIVE_FILE_NAME])
          callGAPI(drive.files(), u'delete', fileId=folder[u'id'])
          deleted_empty = True
        else:
          print convertUTF8(u' not deleting folder {0} because it contains at least 1 item ({1})'.format(folder[DRIVE_FILE_NAME], children[DRIVE_FILES_LIST][0][u'id']))

def emptyDriveTrash(users):
  checkForExtraneousArguments()
  for user in users:
    user, drive = buildDriveGAPIObject(user)
    if not drive:
      continue
    print u'Emptying Drive trash for %s' % user
    callGAPI(drive.files(), u'emptyTrash')

def _showPermission(permission):
  if DRIVE_PERMISSIONS_NAME in permission:
    print convertUTF8(permission[DRIVE_PERMISSIONS_NAME])
  elif u'id' in permission:
    if permission[u'id'] == u'anyone':
      print u'Anyone'
    elif permission[u'id'] == u'anyoneWithLink':
      print u'Anyone with Link'
    else:
      print permission[u'id']
  for key in permission:
    if key in [u'kind', u'etag', u'selfLink', DRIVE_PERMISSIONS_NAME]:
      continue
    print u'  %s: %s' % (key, permission[key])

DRIVEFILE_ACL_ROLES_MAP = {
  u'commenter': u'commenter',
  u'editor': u'writer',
  u'owner': u'owner',
  u'reader': u'reader',
  u'writer': u'writer',
  }

DRIVEFILE_ACL_PERMISSION_TYPES = [u'anyone', u'domain', u'group', u'user',]

def addDriveFileACL(users):
  sendNotificationEmails = False
  emailMessage = None
  fileIdSelection = getDriveFileEntity()
  body, parameters = initializeDriveFileAttributes()
  body[u'type'] = getChoice(DRIVEFILE_ACL_PERMISSION_TYPES)
  if body[u'type'] != u'anyone':
    if body[u'type'] != u'domain':
      body[u'value'] = getEmailAddress()
    else:
      body[u'value'] = getString(OB_DOMAIN_NAME)
    permissionId = body[u'value']
  else:
    permissionId = u'anyone'
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'withlink':
      body[u'withLink'] = True
    elif myarg == u'allowfilediscovery':
      body[u'withLink'] = not getBoolean()
    elif myarg == u'role':
      body[u'role'] = getChoice(DRIVEFILE_ACL_ROLES_MAP, mapChoice=True)
      if body[u'role'] == u'commenter':
        body[u'role'] = u'reader'
        body[u'additionalRoles'] = [u'commenter',]
    elif myarg == u'sendemail':
      sendNotificationEmails = True
    elif myarg == u'emailmessage':
      sendNotificationEmails = True
      emailMessage = getString(OB_STRING)
    else:
      unknownArgumentExit()
  if u'role' not in body:
    missingArgumentExit(u'role {0}'.format(formatChoiceList(DRIVEFILE_ACL_ROLES_MAP)))
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, drive, jcount = validateUserGetFileIDs(user, i, count, fileIdSelection, body, parameters)
    if not drive:
      continue
    if jcount == 0:
      print u'No file ACLs to add for {0}{1}'.format(user, currentCount(i, count))
      continue
    j = 0
    for fileId in fileIdSelection[u'fileIds']:
      j += 1
      print u'Adding permission for %s to file %s%s' % (permissionId, fileId, currentCount(j, jcount))
      result = callGAPI(drive.permissions(), DRIVE_CREATE_PERMISSIONS,
                        fileId=fileId, sendNotificationEmails=sendNotificationEmails, emailMessage=emailMessage, body=body)
      _showPermission(result)

def updateDriveFileACL(users):
  fileIdSelection = getDriveFileEntity()
  body, parameters = initializeDriveFileAttributes()
  isEmail, permissionId = getPermissionId()
  removeExpiration = transferOwnership = None
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'withlink':
      body[u'withLink'] = True
    elif myarg == u'allowfilediscovery':
      body[u'withLink'] = not getBoolean()
    elif myarg == u'role':
      body[u'role'] = getChoice(DRIVEFILE_ACL_ROLES_MAP, mapChoice=True)
      if body[u'role'] == u'commenter':
        body[u'role'] = u'reader'
        body[u'additionalRoles'] = [u'commenter',]
    elif myarg == u'removeexpiration':
      removeExpiration = getBoolean()
    elif myarg == u'transferownership':
      transferOwnership = getBoolean()
    else:
      unknownArgumentExit()
  if removeExpiration is None and u'role' not in body:
    missingArgumentExit(u'role {0}'.format(formatChoiceList(DRIVEFILE_ACL_ROLES_MAP)))
  if isEmail:
    permissionId = validateUserGetPermissionId(permissionId)
    if not permissionId:
      return
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, drive, jcount = validateUserGetFileIDs(user, i, count, fileIdSelection, body, parameters)
    if not drive:
      continue
    if jcount == 0:
      print u'No file ACLs to update for %s' % (user)
      continue
    for fileId in fileIdSelection[u'fileIds']:
      print u'Updating permission for %s to file %s' % (permissionId, fileId)
      result = callGAPI(drive.permissions(), DRIVE_PATCH_PERMISSIONS,
                        fileId=fileId, permissionId=permissionId, removeExpiration=removeExpiration, transferOwnership=transferOwnership, body=body)
      _showPermission(result)

def deleteDriveFileACL(users):
  fileIdSelection = getDriveFileEntity()
  body, parameters = initializeDriveFileAttributes()
  isEmail, permissionId = getPermissionId()
  showTitles = checkArgumentPresent(SHOWTITLES_ARGUMENT)
  checkForExtraneousArguments()
  if isEmail:
    permissionId = validateUserGetPermissionId(permissionId)
    if not permissionId:
      return
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, drive, jcount = validateUserGetFileIDs(user, i, count, fileIdSelection, body, parameters)
    if not drive:
      continue
    if jcount == 0:
      print u'No file ACLs to delete for %s' % (user)
      continue
    for fileId in fileIdSelection[u'fileIds']:
      print u'Removing permission for %s from file %s' % (permissionId, fileId)
      callGAPI(drive.permissions(), u'delete', fileId=fileId, permissionId=permissionId)

def showDriveFileACL(users):
  fileIdSelection = getDriveFileEntity()
  body, parameters = initializeDriveFileAttributes()
  showTitles = checkArgumentPresent(SHOWTITLES_ARGUMENT)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, drive, jcount = validateUserGetFileIDs(user, i, count, fileIdSelection, body, parameters)
    if not drive:
      continue
    if jcount == 0:
      print u'User: {0}, No Drive File/Folder ACLs{1}'.format(user, currentCount(i, count))
      continue
    print u'User: {0}, Drive File/Folder ACLs{1}'.format(user, currentCount(i, count))
    j = 0
    for fileId in fileIdSelection[u'fileIds']:
      j += 1
      try:
        fileName = fileId
        entityType = u'Drive File/Folder ID'
        if showTitles:
          result = callGAPI(drive.files(), u'get',
                            throw_reasons=GAPI_DRIVE_THROW_REASONS+[GAPI_FILE_NOT_FOUND],
                            fileId=fileId, fields=DRIVE_FILE_NAME)
          if result and DRIVE_FILE_NAME in result:
            entityType = u'Drive File/Folder'
            fileName = result[DRIVE_FILE_NAME]+u'('+fileId+u')'
        result = callGAPI(drive.permissions(), u'list',
                          throw_reasons=GAPI_DRIVE_THROW_REASONS+[GAPI_FILE_NOT_FOUND],
                          fileId=fileId)
        print u'{0}: {1}, {2}{3}'.format(entityType, fileName, u'Permittees', currentCount(j, jcount))
        for permission in result[DRIVE_PERMISSIONS_LIST]:
          _showPermission(permission)
      except GAPI_fileNotFound:
        print u'User: {0}, {1}: {2}, Does not exist{3}'.format(user, entityType, fileName, currentCount(j, jcount))
      except (GAPI_serviceNotAvailable, GAPI_authError):
        entityServiceNotApplicableWarning(u'User', user, i, count)
        break

def deleteUsersAliases(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user = normalizeEmailAddressOrUID(user)
    user_aliases = callGAPI(cd.users(), u'get', userKey=user, fields=u'aliases,id,primaryEmail')
    user_id = user_aliases[u'id']
    user_primary = user_aliases[u'primaryEmail']
    if u'aliases' in user_aliases:
      jcount = len(user_aliases[u'aliases'])
      print u'User: {0} has {1} aliases{2}' .format(user_primary, jcount, currentCount(i, count))
      j = 0
      for an_alias in user_aliases[u'aliases']:
        j += 1
        print u'  User: {0}, removing alias {1}{2}'.format(user_primary, an_alias, currentCount(j, jcount))
        callGAPI(cd.users().aliases(), u'delete', userKey=user_id, alias=an_alias)
    else:
      print u'%s has no aliases' % user_primary

def addUserToGroups(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  role = getChoice(GROUP_ROLES_MAP, defaultChoice=ROLE_MEMBER, mapChoice=True)
  lowerRole = role.lower()
  groupList = [normalizeEmailAddressOrUID(group) for group in getStringReturnInList(OB_GROUP_ENTITY)]
  jcount = len(groupList)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user = normalizeEmailAddressOrUID(user)
    if user.find(u'@') != -1:
      body = {u'role': role, u'email': user}
    else:
      body = {u'role': role, u'id': user}
    print u'User: {0}, add to {1} groups as {2}{3}'.format(user, jcount, lowerRole, currentCount(i, count))
    j = 0
    for group in groupList:
      j += 1
      print u'  User: {0}, adding to {1}{2}'.format(user, group, currentCount(j, jcount))
      callGAPI(cd.members(), u'insert', soft_errors=True, groupKey=group, body=body)

def deleteUserFromGroups(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  if CL_argvI < CL_argvLen:
    groupList = [normalizeEmailAddressOrUID(group) for group in getStringReturnInList(OB_GROUP_ENTITY)]
    jcount = len(groupList)
    checkForExtraneousArguments()
  else:
    groupList = None
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user = normalizeEmailAddressOrUID(user)
    if not groupList:
      result = callGAPIpages(cd.groups(), u'list', u'groups', userKey=user, fields=u'groups(email)')
      userGroupList = [item[u'email'] for item in result]
      jcount = len(userGroupList)
    else:
      userGroupList = groupList
    print u'User: {0}, remove from {1} groups{2}'.format(user, jcount, currentCount(i, count))
    j = 0
    for group in userGroupList:
      j += 1
      print u'  User: {0}, removing from {1}{2}'.format(user, group, currentCount(j, jcount))
      callGAPI(cd.members(), u'delete', soft_errors=True, groupKey=group, memberKey=user)

LICENSE_SKUID = u'skuId'
LICENSE_PRODUCTID = u'productId'
LICENSE_OLDSKUID = u'oldSkuId'

def getLicenseParameters(operation):
  lic = buildGAPIObject(GAPI_LICENSING_API)
  parameters = {}
  parameters[LICENSE_SKUID] = getGoogleSKUMap()
  parameters[LICENSE_PRODUCTID] = GOOGLE_SKUS[parameters[LICENSE_SKUID]]
  if operation == u'patch':
    checkArgumentPresent(FROM_ARGUMENT)
    parameters[LICENSE_OLDSKUID] = getGoogleSKUMap(matchProduct=parameters[LICENSE_PRODUCTID])
  checkForExtraneousArguments()
  return (lic, parameters)

def processLicense(users, operation):
  lic, parameters = getLicenseParameters(operation)
  for user in users:
    user = normalizeEmailAddressOrUID(user)
    if operation == u'delete':
      callGAPI(lic.licenseAssignments(), operation,
               soft_errors=True,
               productId=parameters[LICENSE_PRODUCTID], skuId=parameters[LICENSE_SKUID], userId=user)
    elif operation == u'insert':
      callGAPI(lic.licenseAssignments(), operation,
               soft_errors=True,
               productId=parameters[LICENSE_PRODUCTID], skuId=parameters[LICENSE_SKUID], body={u'userId': user})
    elif operation == u'patch':
      callGAPI(lic.licenseAssignments(), operation,
               soft_errors=True,
               productId=parameters[LICENSE_PRODUCTID], skuId=parameters[LICENSE_OLDSKUID], userId=user, body={u'skuId': parameters[LICENSE_SKUID]})

def updatePhoto(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  filenamePattern = getString(OB_PHOTO_FILENAME_PATTERN)
  checkForExtraneousArguments()
  p = re.compile(u'^(ht|f)tps?://.*$')
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, userName, _ = splitEmailAddressOrUID(user)
    filename = filenamePattern.replace(u'#user#', user)
    filename = filename.replace(u'#email#', user)
    filename = filename.replace(u'#username#', userName)
    print u"Updating photo for %s with %s%s" % (user, filename, currentCount(i, count))
    if p.match(filename):
      import urllib2
      try:
        with urllib2.urlopen(filename) as f:
          image_data = str(f.read())
      except urllib2.HTTPError as e:
        print e
        continue
    else:
      image_data = readFile(filename, continueOnError=True, displayError=True)
      if image_data is None:
        continue
    image_data = base64.urlsafe_b64encode(image_data)
    body = {u'photoData': image_data}
    callGAPI(cd.users().photos(), u'update', soft_errors=True, userKey=user, body=body)

def deletePhoto(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user = normalizeEmailAddressOrUID(user)
    print u"Deleting photo for %s%s" % (user, currentCount(i, count))
    callGAPI(cd.users().photos(), u'delete', userKey=user)

def getPhoto(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  targetFolder = os.getcwd()
  showPhotoData = True
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'drivedir':
      targetFolder = GC_Values[GC_DRIVE_DIR]
    elif myarg == u'targetfolder':
      targetFolder = os.path.expanduser(getString(OB_FILE_PATH))
      if not os.path.isdir(targetFolder):
        os.makedirs(targetFolder)
    elif myarg == u'noshow':
      showPhotoData = False
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user = normalizeEmailAddressOrUID(user)
    filename = os.path.join(targetFolder, u'{0}.jpg'.format(user))
    print u"Saving photo to %s%s" % (filename, currentCount(i, count))
    try:
      photo = callGAPI(cd.users().photos(), u'get', throw_reasons=[GAPI_NOT_FOUND], userKey=user)
    except GAPI_notFound:
      print u' no photo for %s' % user
      continue
    try:
      photo_data = str(photo[u'photoData'])
      if showPhotoData:
        print photo_data
      photo_data = base64.urlsafe_b64decode(photo_data)
    except KeyError:
      print u' no photo for %s' % user
      continue
    writeFile(filename, photo_data, continueOnError=True)

PROFILE_SHARING_CHOICES_MAP = {
  u'share': True,
  u'shared': True,
  u'unshare': False,
  u'unshared': False,
  }

def setProfile(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  body = {u'includeInGlobalAddressList': getChoice(PROFILE_SHARING_CHOICES_MAP, mapChoice=True)}
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user = normalizeEmailAddressOrUID(user)
    print u'User: {0}, Setting Profile Sharing to {1}{2}'.format(user, body[u'includeInGlobalAddressList'], currentCount(i, count))
    callGAPI(cd.users(), u'patch', soft_errors=True, userKey=user, body=body)

def showProfile(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user = normalizeEmailAddressOrUID(user)
    result = callGAPI(cd.users(), u'get', userKey=user, fields=u'includeInGlobalAddressList')
    try:
      print u'User: %s  Profile Sharing: %s%s' % (user, result[u'includeInGlobalAddressList'], currentCount(i, count))
    except IndexError:
      pass

def commonClientIds(clientId):
  if clientId == u'gasmo':
    return u'1095133494869.apps.googleusercontent.com'
  return clientId

def deleteTokens(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  checkArgumentPresent(CLIENTID_ARGUMENT, required=True)
  clientId = commonClientIds(getString(OB_CLIENT_ID))
  checkForExtraneousArguments()
  clientId = commonClientIds(clientId)
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user = normalizeEmailAddressOrUID(user)
    callGAPI(cd.tokens(), u'delete', userKey=user, clientId=clientId)
    print u'Deleted token %s for %s%s' % (clientId, user, currentCount(i, count))

def printShowTokens(entityType, users, csvFormat):
  def _showToken(token, j, jcount):
    print u'  Client ID: %s%s' % (token[u'clientId'], currentCount(j, jcount))
    for item in token:
      if item not in [u'clientId', u'scopes']:
        print convertUTF8(u'    %s: %s' % (item, token.get(item, u'')))
    item = u'scopes'
    print u'    %s:' % item
    for it in token.get(item, []):
      print u'      %s' % it

  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  if csvFormat:
    todrive = False
    titles = [u'user', u'clientId', u'displayText', u'anonymous', u'nativeApp', u'userKey', u'scopes']
    csvRows = []
  clientId = None
  delimiter = GC_Values[GC_CSV_OUTPUT_FIELD_DELIMITER]
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if csvFormat and myarg == u'todrive':
      todrive = True
    elif myarg == u'clientid':
      clientId = commonClientIds(getString(OB_CLIENT_ID))
    elif myarg == u'delimiter':
      delimiter = getString(OB_STRING, minLen=1, maxLen=1)
    elif not entityType:
      putArgumentBack()
      entityType, users = getEntityToModify()
  if not entityType:
    users = getUsersToModify(u'all', u'users')
  fields = u','.join([u'clientId', u'displayText', u'anonymous', u'nativeApp', u'userKey', u'scopes'])
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user = normalizeEmailAddressOrUID(user)
    try:
      if csvFormat:
        sys.stderr.write(u'Getting Access Tokens for %s%s' % (user, currentCountNL(i, count)))
      if clientId:
        results = [callGAPI(cd.tokens(), u'get',
                            throw_reasons=[GAPI_NOT_FOUND, GAPI_USER_NOT_FOUND],
                            userKey=user, clientId=clientId, fields=fields)]
      else:
        results = callGAPIitems(cd.tokens(), u'list', u'items',
                                throw_reasons=[GAPI_USER_NOT_FOUND],
                                userKey=user, fields=u'items({0})'.format(fields))
      jcount = len(results)
      if not csvFormat:
        print u'User: {0}, Access Tokens{1}'.format(user, currentCount(i, count))
        if jcount == 0:
          continue
        j = 0
        for token in results:
          j += 1
          _showToken(token, j, jcount)
      else:
        if jcount == 0:
          continue
        for token in results:
          row = {u'user': user, u'scopes': delimiter.join(token.get(u'scopes', []))}
          for item in token:
            if item not in [u'scopes']:
              row[item] = token.get(item, u'')
          csvRows.append(row)
    except (GAPI_notFound, GAPI_userNotFound):
      pass
  if csvFormat:
    writeCSVfile(csvRows, titles, u'OAuth Tokens', todrive)

def deprovisionUser(users):
  cd = buildGAPIObject(GAPI_DIRECTORY_API)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user = normalizeEmailAddressOrUID(user)
    sys.stderr.write(u'Getting Application Specific Passwords for %s%s' % (user, currentCountNL(i, count)))
    asps = callGAPIitems(cd.asps(), u'list', u'items', userKey=user, fields=u'items/codeId')
    jcount = len(asps)
    if jcount > 0:
      j = 0
      for asp in asps:
        j += 1
        print u'  deleting ASP%s' % currentCount(j, jcount)
        callGAPI(cd.asps(), u'delete', userKey=user, codeId=asp[u'codeId'])
    else:
      print u'  No ASPs'
    print u'Invalidating 2SV Backup Codes for %s%s' % (user, currentCount(i, count))
    try:
      callGAPI(cd.verificationCodes(), u'invalidate', soft_errors=True, throw_reasons=[GAPI_INVALID], userKey=user)
    except GAPI_invalid:
      print u'  No 2SV Backup Codes'
    sys.stderr.write(u'Getting Access Tokens for %s%s' % (user, currentCountNL(i, count)))
    tokens = callGAPIitems(cd.tokens(), u'list', u'items', userKey=user, fields=u'items/clientId')
    jcount = len(tokens)
    if jcount > 0:
      j = 0
      for token in tokens[u'items']:
        j += 1
        print u'  deleting token%s' % currentCount(j, jcount)
        callGAPI(cd.tokens(), u'delete', userKey=user, clientId=token[u'clientId'])
    else:
      print u'  No Tokens'
    print u'Done deprovisioning %s%s' % (user, currentCount(i, count))

def printShowGmailProfile(users, csvFormat):
  if csvFormat:
    todrive = False
    titles = []
    csvRows = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if csvFormat and myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    if csvFormat:
      sys.stderr.write(u'Getting Gmail profile for %s%s' % (user, currentCountNL(i, count)))
    try:
      results = callGAPI(gmail.users(), u'getProfile',
                         throw_reasons=GAPI_GMAIL_THROW_REASONS,
                         userId=u'me')
      if results:
        if not csvFormat:
          print u'User: {0}, historyId: {1}, messagesTotal: {2}, threadsTotal: {3}{4}'.format(user, results[u'historyId'], results[u'messagesTotal'], results[u'threadsTotal'], currentCount(i, count))
        else:
          addRowTitlesToCSVfile(results, csvRows, titles)
    except (GAPI_serviceNotAvailable, GAPI_badRequest):
      entityServiceNotApplicableWarning(u'User', user, i, count)
  if csvFormat:
    sortCSVTitles([u'emailAddress',], titles)
    writeCSVfile(csvRows, titles, list_type=u'Gmail Profiles', todrive=todrive)

PROFILE_PROPERTY_PRINT_ORDER = [
  u'objectType',
  u'displayName',
  u'name',
  u'nickname',
  u'domain',
  u'birthday',
  u'ageRange',
  u'gender',
  u'relationshipStatus',
  u'placesLived',
  u'language',
  u'occupation',
  u'aboutMe',
  u'braggingRights',
  u'skills',
  u'tagline',
  u'circledByCount',
  u'plusOneCount',
  u'verified',
  u'emails',
  u'organizations',
  u'urls',
  u'cover',
  ]

PROFILE_ARRAY_PROPERTY_PRINT_ORDER = {
  u'ageRange': [u'min', u'max'],
  u'cover': [u'layout', u'coverPhoto', u'coverInfo'],
  u'coverInfo': [u'topImageOffset', u'leftImageOffset'],
  u'coverPhoto': [u'url', u'height', u'width'],
  u'emails': [u'type', u'value'],
  u'image': [u'url',],
  u'name': [u'formatted', u'honorificPrefix', u'givenName', u'middleName', u'familyName', u'honorificSuffix'],
  u'organizations': [u'type', u'name', u'title', u'department', u'location', u'description', u'startDate', u'endDate', u'primary'],
  u'placesLived': [u'value', u'primary'],
  u'urls': [u'label', u'type', u'value'],
  }

def _showGplusProfile(user, i, count, result):
  def _showProfileObject(spacing, object_name, object_value, object_order=None, level=0):
    if object_name is not None:
      printJSONKey(spacing, object_name)
    if isinstance(object_value, list):
      if object_name is not None:
        printBlankLine()
        spacing += u'  '
      for sub_value in object_value:
        if isinstance(sub_value, (str, unicode, int, bool)):
          printKeyValueList(spacing, [sub_value])
        else:
          _showProfileObject(spacing, None, sub_value, object_order=PROFILE_ARRAY_PROPERTY_PRINT_ORDER[object_name], level=level+1)
      if object_name is not None:
        spacing = spacing[:-2]
    elif isinstance(object_value, dict):
      indentAfterFirst = unindentAfterLast = False
      if object_name is not None:
        printBlankLine()
        spacing += u'  '
      elif level > 0:
        indentAfterFirst = unindentAfterLast = True
      for sub_object in object_order or PROFILE_ARRAY_PROPERTY_PRINT_ORDER[object_name]:
        value = object_value.get(sub_object)
        if value is not None:
          _showProfileObject(spacing, sub_object, value, level=level+1)
          if indentAfterFirst:
            spacing += u'  '
            indentAfterFirst = False
      if object_name is not None or unindentAfterLast:
        spacing = spacing[:-2]
    else:
      if object_name in [u'aboutMe',]:
        printJSONValue(dehtml(object_value))
      else:
        printJSONValue(object_value)

  enabled = result[u'isPlusUser']
  print u'User: {0}, Gplus Profile: {1}{2}'.format(user, result[u'id'], currentCount(i, count))
  spacing = u'  '
  printKeyValueList(spacing, [u'isPlusUser', enabled])
  for item in PROFILE_PROPERTY_PRINT_ORDER:
    value = result.get(item)
    if value is not None:
      _showProfileObject(spacing, item, value)

def printShowGplusProfile(users, csvFormat):
  if csvFormat:
    todrive = False
    titles = []
    csvRows = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if csvFormat and myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gplus = buildGplusGAPIObject(user)
    if not gplus:
      continue
    if csvFormat:
      sys.stderr.write(u'Getting Gplus profile for %s%s' % (user, currentCountNL(i, count)))
    try:
      results = callGAPI(gplus.people(), u'get',
                         throw_reasons=GAPI_GPLUS_THROW_REASONS,
                         userId=u'me')
      if results:
        if not csvFormat:
          _showGplusProfile(user, i, count, results)
        else:
          row = {u'emailAddress': user}
          addRowTitlesToCSVfile(flattenJSON(results, flattened=row), csvRows, titles)
    except (GAPI_serviceNotAvailable, GAPI_badRequest):
      entityServiceNotApplicableWarning(u'User', user, i, count)
  if csvFormat:
    sortCSVTitles([u'emailAddress', u'id', u'displayName', u'domain'], titles)
    writeCSVfile(csvRows, titles, list_type=u'Gplus Profiles', todrive=todrive)

def _getUserGmailLabels(gmail, user, i, count, **kwargs):
  try:
    labels = callGAPI(gmail.users().labels(), u'list',
                      throw_reasons=GAPI_GMAIL_THROW_REASONS,
                      userId=u'me', **kwargs)
    if not labels:
      labels = {u'labels': []}
    return labels
  except (GAPI_serviceNotAvailable, GAPI_badRequest):
    entityServiceNotApplicableWarning(u'User', user, i, count)
    return None

def _getLabelId(labels, labelName):
  for label in labels[u'labels']:
    if label[u'id'] == labelName or label[u'name'] == labelName:
      return label[u'id']
  return None

def _getLabelName(labels, labelId):
  for label in labels[u'labels']:
    if label[u'id'] == labelId:
      return label[u'name']
  return labelId

LABEL_LABEL_LIST_VISIBILITY_CHOICES_MAP = {
  u'hide': u'labelHide',
  u'show': u'labelShow',
  u'showifunread': u'labelShowIfUnread',
  }
LABEL_MESSAGE_LIST_VISIBILITY_CHOICES = [u'hide', u'show',]

def addLabel(users):
  label = getString(OB_LABEL_NAME)
  body = {u'name': label}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'labellistvisibility':
      body[u'labelListVisibility'] = getChoice(LABEL_LABEL_LIST_VISIBILITY_CHOICES_MAP, mapChoice=True)
    elif myarg == u'messagelistvisibility':
      body[u'messageListVisibility'] = getChoice(LABEL_MESSAGE_LIST_VISIBILITY_CHOICES)
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    print u"Creating label %s for %s%s" % (label, user, currentCount(i, count))
    callGAPI(gmail.users().labels(), u'create', soft_errors=True, userId=user, body=body)

def updateLabelSettings(users):
  label_name = getString(OB_LABEL_NAME)
  label_name_lower = label_name.lower()
  body = {}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'name':
      body[u'name'] = getString(OB_STRING)
    elif myarg == u'messagelistvisibility':
      body[u'messageListVisibility'] = getChoice(LABEL_MESSAGE_LIST_VISIBILITY_CHOICES)
    elif myarg == u'labellistvisibility':
      body[u'labelListVisibility'] = getChoice(LABEL_LABEL_LIST_VISIBILITY_CHOICES_MAP, mapChoice=True)
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    labels = _getUserGmailLabels(gmail, user, i, count, fields=u'labels(id,name)')
    if not labels:
      continue
    for label in labels[u'labels']:
      if label[u'name'].lower() == label_name_lower:
        callGAPI(gmail.users().labels(), u'patch', soft_errors=True,
                 userId=user, id=label[u'id'], body=body)
        break
    else:
      print u'Error: user does not have a label named %s' % label_name

def updateLabels(users):
  search = u'^Inbox/(.*)$'
  replace = u'%s'
  merge = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'search':
      search = getString(OB_RE_PATTERN)
    elif myarg == u'replace':
      replace = getString(OB_LABEL_REPLACEMENT)
    elif myarg == u'merge':
      merge = True
    else:
      unknownArgumentExit()
  pattern = re.compile(search, re.IGNORECASE)
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    labels = _getUserGmailLabels(gmail, user, i, count, fields=u'labels(id,name,type)')
    if not labels:
      continue
    for label in labels[u'labels']:
      if label[u'type'] == u'system':
        continue
      match_result = re.search(pattern, label[u'name'])
      if match_result is not None:
        new_label_name = replace % match_result.groups()
        print u' Renaming "%s" to "%s"' % (label[u'name'], new_label_name)
        try:
          callGAPI(gmail.users().labels(), u'patch', soft_errors=True, throw_reasons=[GAPI_ABORTED], id=label[u'id'], userId=user, body={u'name': new_label_name})
        except GAPI_aborted:
          if merge:
            print u'  Merging %s label to existing %s label' % (label[u'name'], new_label_name)
            q = u'label:"%s"' % label[u'name']
            messages_to_relabel = callGAPIpages(gmail.users().messages(), u'list', u'messages', userId=user, q=q)
            if len(messages_to_relabel) > 0:
              for new_label in labels[u'labels']:
                if new_label[u'name'].lower() == new_label_name.lower():
                  new_label_id = new_label[u'id']
                  body = {u'addLabelIds': [new_label_id]}
                  break
              j = 1
              for message_to_relabel in messages_to_relabel:
                print u'    relabeling message %s%s' % (message_to_relabel[u'id'], currentCount(j, len(messages_to_relabel)))
                callGAPI(gmail.users().messages(), u'modify', userId=user, id=message_to_relabel[u'id'], body=body)
                j += 1
            else:
              print u'   no messages with %s label' % label[u'name']
            print u'   Deleting label %s' % label[u'name']
            callGAPI(gmail.users().labels(), u'delete', id=label[u'id'], userId=user)
          else:
            print u'  Error: looks like %s already exists, not renaming. Use the "merge" argument to merge the labels' % new_label_name

def deleteLabel(users):
  def gmail_del_result(request_id, response, exception):
    if exception:
      print exception

  label = getString(OB_LABEL_NAME)
  label_name_lower = label.lower()
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    sys.stderr.write(u'Getting all labels for %s%s' % (user, currentCountNL(i, count)))
    labels = callGAPI(gmail.users().labels(), u'list', userId=user, fields=u'labels(id,name,type)')
    del_labels = []
    if label == u'--ALL_LABELS--':
      for del_label in labels[u'labels']:
        if del_label[u'type'] == u'system':
          continue
        del_labels.append(del_label)
    elif label[:6].lower() == u'regex:':
      regex = label[6:]
      p = re.compile(regex)
      for del_label in labels[u'labels']:
        if del_label[u'type'] == u'system':
          continue
        elif p.match(del_label[u'name']):
          del_labels.append(del_label)
    else:
      for del_label in labels[u'labels']:
        if label_name_lower == del_label[u'name'].lower():
          del_labels.append(del_label)
          break
      else:
        print u' Error: no such label for %s' % user
        continue
    j = 0
    del_me_count = len(del_labels)
    dbatch = googleapiclient.http.BatchHttpRequest()
    for del_me in del_labels:
      j += 1
      print u' deleting label %s%s' % (del_me[u'name'], currentCount(j, del_me_count))
      dbatch.add(gmail.users().labels().delete(userId=user, id=del_me[u'id']), callback=gmail_del_result)
      if len(dbatch._order) == 10:
        dbatch.execute()
        dbatch = googleapiclient.http.BatchHttpRequest()
    if len(dbatch._order) > 0:
      dbatch.execute()

def showLabels(users):
  onlyUser = showCounts = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'onlyuser':
      onlyUser = True
    elif myarg == u'showcounts':
      showCounts = True
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    labels = callGAPI(gmail.users().labels(), u'list', userId=user, soft_errors=True)
    if labels:
      print u'User: {0}, Labels:{1}'.format(user, currentCount(i, count))
      for label in labels[u'labels']:
        if onlyUser and (label[u'type'] == u'system'):
          continue
        print convertUTF8(u'  {0}'.format(label[u'name']))
        for a_key in label:
          if a_key == u'name':
            continue
          print u'   %s: %s' % (a_key, label[a_key])
        if showCounts:
          counts = callGAPI(gmail.users().labels(), u'get',
                            userId=user, id=label[u'id'],
                            fields=u'messagesTotal,messagesUnread,threadsTotal,threadsUnread')
          for a_key in counts:
            print u'   %s: %s' % (a_key, counts[a_key])

def labelsToLabelIds(gmail, labels):
  allLabels = {
    u'INBOX': u'INBOX', u'SPAM': u'SPAM', u'TRASH': u'TRASH',
    u'UNREAD': u'UNREAD', u'STARRED': u'STARRED', u'IMPORTANT': u'IMPORTANT',
    u'SENT': u'SENT', u'DRAFT': u'DRAFT',
    u'CATEGORY_PERSONAL': u'CATEGORY_PERSONAL',
    u'CATEGORY_SOCIAL': u'CATEGORY_SOCIAL',
    u'CATEGORY_PROMOTIONS': u'CATEGORY_PROMOTIONS',
    u'CATEGORY_UPDATES': u'CATEGORY_UPDATES',
    u'CATEGORY_FORUMS': u'CATEGORY_FORUMS',
    }
  labelIds = []
  for label in labels:
    if label not in allLabels:
      # first refresh labels in user mailbox
      label_results = callGAPI(gmail.users().labels(), u'list',
                               userId=u'me', fields=u'labels(id,name,type)')
      for a_label in label_results[u'labels']:
        if a_label[u'type'] == u'system':
          allLabels[a_label[u'id']] = a_label[u'id']
        else:
          allLabels[a_label[u'name']] = a_label[u'id']
    if label not in allLabels:
      # if still not there, create it
      label_results = callGAPI(gmail.users().labels(), u'create',
                               body={u'labelListVisibility': u'labelShow',
                                     u'messageListVisibility': u'show', u'name': label},
                               userId=u'me', fields=u'id')
      allLabels[label] = label_results[u'id']
    try:
      labelIds.append(allLabels[label])
    except KeyError:
      pass
    if label.find(u'/') != -1:
      # make sure to create parent labels for proper nesting
      parent_label = label[:label.rfind(u'/')]
      while True:
        if not parent_label in allLabels:
          label_result = callGAPI(gmail.users().labels(), u'create',
                                  userId=u'me', body={u'name': parent_label})
          allLabels[parent_label] = label_result[u'id']
        if parent_label.find(u'/') == -1:
          break
        parent_label = parent_label[:parent_label.rfind(u'/')]
  return labelIds

PROCESS_MESSAGE_FUNCTION_TO_ACTION_MAP = {u'delete': u'deleted', u'modify': u'modified', u'trash': u'trashed', u'untrash': u'untrashed'}

def processMessages(users, function):
  query = None
  doIt = False
  maxToProcess = 1
  body = {}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'query':
      query = getString(OB_QUERY)
    elif myarg == u'doit':
      doIt = True
    elif myarg in [u'maxtodelete', u'maxtomodify', u'maxtotrash', u'maxtountrash']:
      maxToProcess = getInteger(minVal=0)
    elif (function == u'modify') and (myarg == u'addlabel'):
      body.setdefault(u'addLabelIds', [])
      body[u'addLabelIds'].append(getString(OB_LABEL_NAME))
    elif (function == u'modify') and (myarg == u'removelabel'):
      body.setdefault(u'removeLabelIds', [])
      body[u'removeLabelIds'].append(getString(OB_LABEL_NAME))
    else:
      unknownArgumentExit()
  if not query:
    missingArgumentExit(u'query')
  action = PROCESS_MESSAGE_FUNCTION_TO_ACTION_MAP[function]
  for user in users:
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    print u'Searching messages for %s' % user
    page_message = u'Got %%%%total_items%%%% messages for user %s' % user
    listResult = callGAPIpages(gmail.users().messages(), u'list', u'messages', page_message=page_message,
                               userId=u'me', q=query, includeSpamTrash=True, soft_errors=True)
    result_count = len(listResult)
    if not doIt or result_count == 0:
      print u'would try to %s %s messages for user %s (max %s)\n' % (function, result_count, user, maxToProcess)
      continue
    elif result_count > maxToProcess:
      print u'WARNING: refusing to %s ANY messages for %s since max messages to process is %s and messages to be %s is %s\n' % (function, user, maxToProcess, action, result_count)
      continue
    i = 0
    if function == u'delete':
      id_batches = [[]]
      for del_me in listResult:
        id_batches[i].append(del_me[u'id'])
        if len(id_batches[i]) == 1000:
          i += 1
          id_batches.append([])
      deleted_messages = 0
      for id_batch in id_batches:
        print u'deleting %s messages' % len(id_batch)
        callGAPI(gmail.users().messages(), u'batchDelete',
                 body={u'ids': id_batch}, userId=u'me')
        deleted_messages += len(id_batch)
        print u'deleted %s of %s messages' % (deleted_messages, result_count)
      continue
    if not body:
      kwargs = {}
    else:
      kwargs = {u'body': {}}
      for my_key in body:
        kwargs[u'body'][my_key] = labelsToLabelIds(gmail, body[my_key])
    for a_message in listResult:
      i += 1
      print u' %s message %s for user %s%s' % (function, a_message[u'id'], user, currentCount(i, result_count))
      callGAPI(gmail.users().messages(), function,
               id=a_message[u'id'], userId=u'me', **kwargs)

def setArrows(users):
  emailSettings = getEmailSettingsObject()
  enable = getBoolean()
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, userName, emailSettings.domain = splitEmailAddressOrUID(user)
    print u"Setting Personal Indicator Arrows to %s for %s%s" % (str(enable), user, currentCount(i, count))
    callGData(emailSettings, u'UpdateGeneral', soft_errors=True, username=userName, arrows=enable)

def addDelegate(users, checkForTo):
  emailsettings = buildGAPIObject(GAPI_EMAIL_SETTINGS_API)
  if checkForTo:
    checkArgumentPresent(TO_ARGUMENT, required=True)
  delegateEmail, _, _ = splitEmailAddressOrUID(getEmailAddress())
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    delegatorEmail, delegatorName, delegatorDomain = splitEmailAddressOrUID(user)
    uri = u'https://apps-apis.google.com/a/feeds/emailsettings/2.0/%s/%s/delegation' % (delegatorDomain, delegatorName)
    body = u'''<?xml version="1.0" encoding="utf-8"?>
<atom:entry xmlns:atom="http://www.w3.org/2005/Atom" xmlns:apps="http://schemas.google.com/apps/2006">
<apps:property name="address" value="%s" />
</atom:entry>''' % delegateEmail
    headers = {u'GData-Version': u'2.0', u'Content-Type': u'application/atom+xml; charset=UTF-8'}
    print u"Giving {0} delegate access to {1}{2}".format(delegateEmail, delegatorEmail, currentCount(i, count))
    retries = 10
    for n in range(1, retries+1):
      status, result = emailsettings._http.request(uri=uri, method=u'POST', body=body, headers=headers)
      httpStatus = int(status[u'status'])
      if httpStatus == 201: # Success
        time.sleep(10) # on success, sleep 10 seconds before exiting or moving on to next user to prevent ghost delegates
        break
      elif httpStatus > 499:
        waitOnFailure(n, retries, str(httpStatus), result)
      else:
        print u'ERROR: Could not create delegation - %s - %s' % (httpStatus, result)
        sys.exit(3)

def deleteDelegate(users):
  emailsettings = buildGAPIObject(GAPI_EMAIL_SETTINGS_API)
  delegateEmail = getString(OB_EMAIL_ADDRESS)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    delegatorEmail, delegatorName, delegatorDomain = splitEmailAddressOrUID(user)
    delegateEmail = addDomainToEmailAddressOrUID(delegateEmail, delegatorDomain)
    if delegateEmail:
      print u"Deleting %s delegate access to %s%s" % (delegateEmail, delegatorEmail, currentCount(i, count))
      callGAPI(emailsettings.delegates(), u'delete', v=u'2.0', delegate=delegateEmail, delegator=delegatorName, domainName=delegatorDomain)

def printShowDelegates(users, csvFormat):
  emailsettings = buildGAPIObject(GAPI_EMAIL_SETTINGS_API)
  if csvFormat:
    todrive = False
    csvRows = []
    titles = [u'User', u'delegateName', u'delegateAddress', u'delegationStatus']
  else:
    csvStyle = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if not csvFormat and myarg == u'csv':
      csvStyle = True
    elif csvFormat and myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    delegatorEmail, delegatorName, delegatorDomain = splitEmailAddressOrUID(user)
    if csvFormat:
      sys.stderr.write(u"Getting delegates for %s%s" % (delegatorEmail, currentCountNL(i, count)))
    result = callGAPI(emailsettings.delegates(), u'get', soft_errors=True, v=u'2.0', domainName=delegatorDomain, delegator=delegatorName)
    delegates = result.get(u'feed', {}).get(u'entry', []) if result else []
    jcount = len(delegates)
    if jcount > 0:
      if not csvFormat and not csvStyle:
        print u'Delegator: {0}, Delegates:{1}'.format(delegatorEmail, currentCount(i, count))
      j = 0
      for delegate in delegates:
        j += 1
        status = u''
        delegateAddress = u''
        delegateName = u''
        delegationId = u''
        for item in delegate[u'apps$property']:
          if item[u'name'] == u'status':
            status = item[u'value']
          elif item[u'name'] == u'address':
            delegateAddress = item[u'value']
          elif item[u'name'] == u'delegate':
            delegateName = item[u'value']
          elif item[u'name'] == u'delegationId':
            delegationId = item[u'value']
        if csvFormat:
          row = {u'User': user, u'delegateName': delegateName, u'delegateAddress': delegateAddress, u'delegationStatus': status}
          csvRows.append(row)
        elif csvStyle:
          print u'%s,%s,%s' % (delegatorEmail, delegateAddress, status)
        else:
          print convertUTF8(u'  Delegate: {0}{1}'.format(delegateName, currentCount(j, jcount)))
          print u'    Status: {0}'.format(status)
          print u'    Delegate Email: {0}'.format(delegateAddress)
          print u'    Delegate ID: {0}'.format(delegationId)
  if csvFormat:
    writeCSVfile(csvRows, titles, u'Delegates', todrive)

FILTER_ADD_LABEL_TO_ARGUMENT_MAP = {
  u'IMPORTANT': u'important',
  u'STARRED': u'star',
  u'TRASH': u'trash',
  }

FILTER_REMOVE_LABEL_TO_ARGUMENT_MAP = {
  u'IMPORTANT': u'notimportant',
  u'UNREAD': u'markread',
  u'INBOX': u'archive',
  u'SPAM': u'neverspam',
  }

def _printFilter(user, userFilter, labels):
  row = {u'User': user, u'id': userFilter[u'id']}
  if u'criteria' in userFilter:
    for item in userFilter[u'criteria']:
      if item in [u'hasAttachment', u'excludeChats']:
        row[item] = item
      elif item == u'size':
        row[item] = u'size {0} {1}'.format(userFilter[u'criteria'][u'sizeComparison'], formatMaxMessageBytes(userFilter[u'criteria'][item]))
      elif item == u'sizeComparison':
        pass
      else:
        row[item] = u'{0} {1}'.format(item, userFilter[u'criteria'][item])
  else:
    row[u'error'] = u'NoCriteria'
  if u'action' in userFilter:
    for labelId in userFilter[u'action'].get(u'addLabelIds', []):
      if labelId in FILTER_ADD_LABEL_TO_ARGUMENT_MAP:
        row[FILTER_ADD_LABEL_TO_ARGUMENT_MAP[labelId]] = FILTER_ADD_LABEL_TO_ARGUMENT_MAP[labelId]
      else:
        row[u'label'] = u'label {0}'.format(_getLabelName(labels, labelId))
    for labelId in userFilter[u'action'].get(u'removeLabelIds', []):
      if labelId in FILTER_REMOVE_LABEL_TO_ARGUMENT_MAP:
        row[FILTER_REMOVE_LABEL_TO_ARGUMENT_MAP[labelId]] = FILTER_REMOVE_LABEL_TO_ARGUMENT_MAP[labelId]
    if userFilter[u'action'].get(u'forward'):
      row[u'forward'] = u'forward {0}'.format(userFilter[u'action'][u'forward'])
  else:
    row[u'error'] = u'NoActions'
  return row

def _showFilter(userFilter, j, jcount, labels):
  print u'  Filter: {0}{1}'.format(userFilter[u'id'], currentCount(j, jcount))
  print u'    Criteria:'
  if u'criteria' in userFilter:
    for item in userFilter[u'criteria']:
      if item in [u'hasAttachment', u'excludeChats']:
        print u'      {0}'.format(item)
      elif item == u'size':
        print u'      {0} {1} {2}'.format(item, userFilter[u'criteria'][u'sizeComparison'], userFilter[u'criteria'][item])
      elif item == u'sizeComparison':
        pass
      else:
        print convertUTF8(u'      {0} "{1}"'.format(item, userFilter[u'criteria'][item]))
  else:
    printKeyValueList(u'      ', [ERROR, PHRASE_NO_FILTER_CRITERIA.format(u'Filter')])
  print u'    Actions:'
  if u'action' in userFilter:
    for labelId in userFilter[u'action'].get(u'addLabelIds', []):
      if labelId in FILTER_ADD_LABEL_TO_ARGUMENT_MAP:
        print u'      {0}'.format(FILTER_ADD_LABEL_TO_ARGUMENT_MAP[labelId])
      else:
        print convertUTF8(u'      label "{0}"'.format(_getLabelName(labels, labelId)))
    for labelId in userFilter[u'action'].get(u'removeLabelIds', []):
      if labelId in FILTER_REMOVE_LABEL_TO_ARGUMENT_MAP:
        print u'      {0}'.format(FILTER_REMOVE_LABEL_TO_ARGUMENT_MAP[labelId])
    if userFilter[u'action'].get(u'forward'):
      print u'    Forwarding Address: {0}'.format(userFilter[u'action'][u'forward'])
  else:
    printKeyValueList(u'      ', [ERROR, PHRASE_NO_FILTER_ACTIONS.format(u'Filter')])
#
FILTER_CRITERIA_CHOICES_MAP = {
  u'excludechats': u'excludeChats',
  u'from': u'from',
  u'hasattachment': u'hasAttachment',
  u'haswords': u'query',
  u'musthaveattachment': u'hasAttachment',
  u'negatedquery': u'negatedQuery',
  u'nowords': u'negatedQuery',
  u'query': u'query',
  u'size': u'size',
  u'subject': u'subject',
  u'to': u'to',
  }
FILTER_ACTION_CHOICES = [u'archive', u'forward', u'important', u'label', u'markread', u'neverspam', u'notimportant', u'star', u'trash',]

def addFilter(users):
  body = {}
  addLabelName = None
  addLabelIds = []
  removeLabelIds = []
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg in FILTER_CRITERIA_CHOICES_MAP:
      myarg = FILTER_CRITERIA_CHOICES_MAP[myarg]
      body.setdefault(u'criteria', {})
      if myarg in [u'from', u'to']:
        body[u'criteria'][myarg] = getEmailAddress(noUid=True)
      elif myarg in [u'subject', u'query', u'negatedQuery']:
        body[u'criteria'][myarg] = getString(OB_STRING)
      elif myarg in [u'hasAttachment', u'excludeChats']:
        body[u'criteria'][myarg] = True
      elif myarg == u'size':
        body[u'criteria'][u'sizeComparison'] = getChoice([u'larger', u'smaller'])
        body[u'criteria'][myarg] = getMaxMessageBytes()
    elif myarg in FILTER_ACTION_CHOICES:
      body.setdefault(u'action', {})
      if myarg == u'label':
        addLabelName = getString(OB_LABEL_NAME)
      elif myarg == u'important':
        addLabelIds.append(u'IMPORTANT')
        if u'IMPORTANT' in removeLabelIds:
          removeLabelIds.remove(u'IMPORTANT')
      elif myarg == u'star':
        addLabelIds.append(u'STARRED')
      elif myarg == u'trash':
        addLabelIds.append(u'TRASH')
      elif myarg == u'notimportant':
        removeLabelIds.append(u'IMPORTANT')
        if u'IMPORTANT' in addLabelIds:
          addLabelIds.remove(u'IMPORTANT')
      elif myarg == u'markread':
        removeLabelIds.append(u'UNREAD')
      elif myarg == u'archive':
        removeLabelIds.append(u'INBOX')
      elif myarg == u'neverspam':
        removeLabelIds.append(u'SPAM')
      elif myarg == u'forward':
        body[u'action'][u'forward'] = getEmailAddress(noUid=True)
    else:
      unknownArgumentExit()
  if u'criteria' not in body:
    missingChoiceExit(FILTER_CRITERIA_CHOICES_MAP)
  if u'action' not in body:
    missingChoiceExit(FILTER_ACTION_CHOICES)
  if removeLabelIds:
    body[u'action'][u'removeLabelIds'] = removeLabelIds
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    labels = _getUserGmailLabels(gmail, user, i, count, fields=u'labels(id,name)')
    if not labels:
      continue
    if addLabelIds:
      body[u'action'][u'addLabelIds'] = addLabelIds[:]
    if addLabelName:
      if not addLabelIds:
        body[u'action'][u'addLabelIds'] = []
      addLabelId = _getLabelId(labels, addLabelName)
      if not addLabelId:
        result = callGAPI(gmail.users().labels(), u'create',
                          soft_errors=True,
                          userId=u'me', body={u'name': addLabelName}, fields=u'id')
        if not result:
          continue
        addLabelId = result[u'id']
      body[u'action'][u'addLabelIds'].append(addLabelId)
    print u"Adding filter for %s%s" % (user, currentCount(i, count))
    result = callGAPI(gmail.users().settings().filters(), u'create',
                      soft_errors=True,
                      userId=u'me', body=body)
    if result:
      print u"User: %s, Filter: %s, Added%s" % (user, result[u'id'], currentCount(i, count))

def deleteFilters(users):
  filterId = getString(OB_FILTER_ID)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    print u"Deleting filter %s for %s%s" % (filterId, user, currentCount(i, count))
    callGAPI(gmail.users().settings().filters(), u'delete',
             soft_errors=True,
             userId=u'me', id=filterId)

def printShowFilters(users, csvFormat):
  if csvFormat:
    todrive = False
    csvRows = []
    titles = [u'User', u'id']
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if csvFormat and myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    labels = _getUserGmailLabels(gmail, user, i, count, fields=u'labels(id,name)')
    if not labels:
      continue
    result = callGAPI(gmail.users().settings().filters(), u'list',
                      soft_errors=True,
                      userId=u'me')
    jcount = len(result.get(u'filter', [])) if (result) else 0
    if not csvFormat:
      print u'User: {0}, Filters:{1}'.format(user, currentCount(i, count))
      if jcount == 0:
        continue
      j = 0
      for userFilter in result[u'filter']:
        j += 1
        _showFilter(userFilter, j, jcount, labels)
    else:
      if jcount == 0:
        continue
      for userFilter in result[u'filter']:
        row = _printFilter(user, userFilter, labels)
        for item in row:
          if item not in titles:
            titles.append(item)
        csvRows.append(row)
  if csvFormat:
    sortCSVTitles([u'User', u'id'], titles)
    writeCSVfile(csvRows, titles, u'Filters', todrive)

def infoFilters(users):
  filterId = getString(OB_FILTER_ID)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    labels = _getUserGmailLabels(gmail, user, i, count, fields=u'labels(id,name)')
    if not labels:
      continue
    result = callGAPI(gmail.users().settings().filters(), u'get',
                      soft_errors=True,
                      userId=u'me', id=filterId)
    if result:
      print u'User: {0}, Filter:{1}'.format(user, currentCount(i, count))
      _showFilter(result, 1, 1, labels)

EMAILSETTINGS_OLD_NEW_OLD_FORWARD_ACTION_MAP = {
  u'ARCHIVE': u'archive',
  u'DELETE': u'trash',
  u'KEEP': u'leaveInInBox',
  u'MARK_READ': u'markRead',
  u'archive': u'ARCHIVE',
  u'trash': u'DELETE',
  u'leaveInInbox': u'KEEP',
  u'markRead': u'MARK_READ',
  }

def setForward(users):
  enable = getBoolean()
  body = {u'enabled': enable}
  if enable:
    while CL_argvI < CL_argvLen:
      myarg = getArgument()
      if myarg in EMAILSETTINGS_FORWARD_POP_ACTION_CHOICES_MAP:
        body[u'disposition'] = EMAILSETTINGS_FORWARD_POP_ACTION_CHOICES_MAP[myarg]
      elif myarg == u'confirm':
        pass
      elif myarg.find(u'@') != -1:
        body[u'emailAddress'] = normalizeEmailAddressOrUID(CL_argv[CL_argvI-1])
      else:
        unknownArgumentExit()
    if not body.get(u'disposition'):
      missingChoiceExit(EMAILSETTINGS_FORWARD_POP_ACTION_CHOICES_MAP)
    if not body.get(u'emailAddress'):
      missingArgumentExit(OB_EMAIL_ADDRESS)
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    if enable:
      print u"User: %s, Forward Enabled: %s, Forwarding Address: %s, Action: %s%s" % (user, enable, body[u'emailAddress'], body[u'disposition'], currentCount(i, count))
    else:
      print u"User: %s, Forward Enabled: %s%s" % (user, enable, currentCount(i, count))
    callGAPI(gmail.users().settings(), u'updateAutoForwarding',
             soft_errors=True,
             userId=u'me', body=body)

def printShowForward(users, csvFormat):
  def _showForward(user, i, count, result):
    if u'enabled' in result:
      enabled = result[u'enabled']
      if enabled:
        print u"User: %s, Forward Enabled: %s, Forwarding Address: %s, Action: %s%s" % (user, enabled, result[u'emailAddress'], result[u'disposition'], currentCount(i, count))
      else:
        print u"User: %s, Forward Enabled: %s%s" % (user, enabled, currentCount(i, count))
    else:
      enabled = result[u'enable'] == u'true'
      if enabled:
        print u"User: %s, Forward Enabled: %s, Forwarding Address: %s, Action: %s%s" % (user, enabled, result[u'forwardTo'], EMAILSETTINGS_OLD_NEW_OLD_FORWARD_ACTION_MAP[result[u'action']], currentCount(i, count))
      else:
        print u"User: %s, Forward Enabled: %s%s" % (user, enabled, currentCount(i, count))

  def _printForward(user, result):
    if u'enabled' in result:
      row = {u'User': user, u'forwardEnabled': result[u'enabled']}
      if result[u'enabled']:
        row[u'forwardTo'] = result[u'emailAddress']
        row[u'disposition'] = result[u'disposition']
    else:
      row = {u'User': user, u'forwardEnabled': result[u'enable']}
      if result[u'enable'] == u'true':
        row[u'forwardTo'] = result[u'forwardTo']
        row[u'disposition'] = EMAILSETTINGS_OLD_NEW_OLD_FORWARD_ACTION_MAP[result[u'action']]
    csvRows.append(row)

  if csvFormat:
    todrive = False
    csvRows = []
    titles = [u'User', u'forwardEnabled', u'forwardTo', u'disposition']
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if csvFormat and myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    result = callGAPI(gmail.users().settings(), u'getAutoForwarding',
                      soft_errors=True,
                      userId=u'me')
    if result:
      if not csvFormat:
        _showForward(user, i, count, result)
      else:
        _printForward(user, result)
  if csvFormat:
    writeCSVfile(csvRows, titles, u'Forward', todrive)

def addForwardingAddresses(users):
  emailAddress = getEmailAddress(noUid=True)
  body = {u'forwardingEmail':  emailAddress}
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    print u"Adding Forwarding Address %s for %s%s" % (emailAddress, user, currentCount(i, count))
    callGAPI(gmail.users().settings().forwardingAddresses(), u'create',
             soft_errors=True,
             userId=u'me', body=body)

def deleteForwardingAddresses(users):
  emailAddress = getEmailAddress(noUid=True)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    print u"Deleting Forwarding Address %s for %s%s" % (emailAddress, user, currentCount(i, count))
    callGAPI(gmail.users().settings().forwardingAddresses(), u'delete',
             soft_errors=True,
             userId=u'me', forwardingEmail=emailAddress)

def infoForwardingAddresses(users):
  emailAddress = getEmailAddress(noUid=True)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    forward = callGAPI(gmail.users().settings().forwardingAddresses(), u'get',
                       soft_errors=True,
                       userId=u'me', forwardingEmail=emailAddress)
    if forward:
      print u'User: {0}, Forwarding Address: {1}, Verification Status: {2}{3}'.format(user, forward[u'forwardingEmail'], forward[u'verificationStatus'], currentCount(i, count))

def printShowForwardingAddresses(users, csvFormat):
  if csvFormat:
    todrive = False
    csvRows = []
    titles = [u'User', u'forwardingEmail', u'verificationStatus']
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if csvFormat and myarg == u'todrive':
      todrive = True
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    result = callGAPI(gmail.users().settings().forwardingAddresses(), u'list',
                      soft_errors=True,
                      userId=u'me')
    jcount = len(result.get(u'forwardingAddresses', [])) if (result) else 0
    if not csvFormat:
      print u'User: {0}, Forwarding Addresses:{1}'.format(user, currentCount(i, count))
      if jcount == 0:
        continue
      j = 0
      for forward in result[u'forwardingAddresses']:
        j += 1
        print u'  Forwarding Address: {0}, Verification Status: {1}{2}'.format(forward[u'forwardingEmail'], forward[u'verificationStatus'], currentCount(j, jcount))
    else:
      if jcount == 0:
        continue
      for forward in result[u'forwardingAddresses']:
        row = {u'User': user, u'forwardingEmail': forward[u'forwardingEmail'], u'verificationStatus': forward[u'verificationStatus']}
        csvRows.append(row)
  if csvFormat:
    writeCSVfile(csvRows, titles, u'Forwarding Addresses', todrive)

EMAILSETTINGS_IMAP_EXPUNGE_BEHAVIOR_CHOICES_MAP = {
  u'archive': u'archive',
  u'deleteforever': u'deleteForever',
  u'trash': u'trash',
  }

EMAILSETTINGS_IMAP_MAX_FOLDER_SIZE_CHOICES = [u'0', u'1000', u'2000', u'5000', u'10000']

def setImap(users):
  enable = getBoolean()
  body = {u'enabled': enable, u'autoExpunge': True, u'expungeBehavior': u'archive', u'maxFolderSize': 0}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'noautoexpunge':
      body[u'autoExpunge'] = False
    elif myarg == u'expungebehavior':
      body[u'expungeBehavior'] = getChoice(EMAILSETTINGS_IMAP_EXPUNGE_BEHAVIOR_CHOICES_MAP, mapChoice=True)
    elif myarg == u'maxfoldersize':
      body[u'maxFolderSize'] = int(getChoice(EMAILSETTINGS_IMAP_MAX_FOLDER_SIZE_CHOICES))
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    print u"Setting IMAP Access to %s for %s%s" % (str(enable), user, currentCount(i, count))
    callGAPI(gmail.users().settings(), u'updateImap',
             soft_errors=True,
             userId=u'me', body=body)

def showImap(users):
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    result = callGAPI(gmail.users().settings(), u'getImap',
                      soft_errors=True,
                      userId=u'me')
    if result:
      enabled = result[u'enabled']
      if enabled:
        print u'User: {0}, IMAP Enabled: {1}, autoExpunge: {2}, expungeBehavior: {3}, maxFolderSize:{4}{5}'.format(user, enabled, result[u'autoExpunge'], result[u'expungeBehavior'], result[u'maxFolderSize'], currentCount(i, count))
      else:
        print u'User: {0}, IMAP Enabled: {1}{2}'.format(user, enabled, currentCount(i, count))

EMAILSETTINGS_POP_ENABLE_FOR_CHOICES_MAP = {
  u'allmail': u'allMail',
  u'fromnowon': u'fromNowOn',
  u'mailfromnowon': u'fromNowOn',
  u'newmail': u'fromNowOn',
  }

EMAILSETTINGS_FORWARD_POP_ACTION_CHOICES_MAP = {
  u'archive': u'archive',
  u'delete': u'trash',
  u'keep': u'leaveInInbox',
  u'leaveininbox': u'leaveInInbox',
  u'markread': u'markRead',
  u'trash': u'trash',
  }

def setPop(users):
  enable = getBoolean()
  body = {u'accessWindow': [u'disabled', u'allMail'][enable], u'disposition': u'leaveInInbox'}
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'for':
      body[u'accessWindow'] = getChoice(EMAILSETTINGS_POP_ENABLE_FOR_CHOICES_MAP, mapChoice=True)
    elif myarg == u'action':
      body[u'disposition'] = getChoice(EMAILSETTINGS_FORWARD_POP_ACTION_CHOICES_MAP, mapChoice=True)
    elif myarg == u'confirm':
      pass
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    print u"Setting POP Access to %s for %s%s" % (str(enable), user, currentCount(i, count))
    callGAPI(gmail.users().settings(), u'updatePop',
             soft_errors=True,
             userId=u'me', body=body)

def showPop(users):
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    result = callGAPI(gmail.users().settings(), u'getPop',
                      soft_errors=True,
                      userId=u'me')
    if result:
      enabled = result[u'accessWindow'] != u'disabled'
      if enabled:
        print u'User: {0}, POP Enabled: {1}, For: {2}, Action: {3}{4}'.format(user, enabled, result[u'accessWindow'], result[u'disposition'], currentCount(i, count))
      else:
        print u'User: {0}, POP Enabled: {1}{2}'.format(user, enabled, currentCount(i, count))

def setLanguage(users):
  emailSettings = getEmailSettingsObject()
  language = getChoice(LANGUAGE_CODES_MAP, mapChoice=True)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, userName, emailSettings.domain = splitEmailAddressOrUID(user)
    print u"Setting the language for %s to %s%s" % (user, language, currentCount(i, count))
    callGData(emailSettings, u'UpdateLanguage', soft_errors=True, username=userName, language=language)

VALID_PAGESIZES = [u'25', u'50', u'100']

def setPageSize(users):
  emailSettings = getEmailSettingsObject()
  PageSize = getChoice(VALID_PAGESIZES)
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, userName, emailSettings.domain = splitEmailAddressOrUID(user)
    print u"Setting Page Size to %s for %s%s" % (PageSize, user, currentCount(i, count))
    callGData(emailSettings, u'UpdateGeneral', soft_errors=True, username=userName, page_size=PageSize)

def _showSendAs(result, j, jcount, formatSig):
  if result[u'displayName']:
    print convertUTF8(u'  SendAs Address: {0} <{1}>{2}'.format(result[u'displayName'], result[u'sendAsEmail'], currentCount(j, jcount)))
  else:
    print convertUTF8(u'  SendAs Address: <{0}>{1}'.format(result[u'sendAsEmail'], currentCount(j, jcount)))
  if result.get(u'replyToAddress'):
    print u'    ReplyTo: {0}'.format(result[u'replyToAddress'])
  print u'    IsPrimary: {0}'.format(result.get(u'isPrimary', False))
  print u'    Default: {0}'.format(result.get(u'isDefault', False))
  if not result.get(u'isPrimary', False):
    print u'    TreatAsAlias: {0}'.format(result.get(u'treatAsAlias', False))
    print u'    Verification Status: {0}'.format(result.get(u'verificationStatus', u'unspecified'))
  sys.stdout.write(u'    Signature:\n      ')
  signature = result.get(u'signature')
  if not signature:
    signature = u'None'
  if formatSig:
    print convertUTF8(indentMultiLineText(dehtml(signature), n=6))
  else:
    print convertUTF8(indentMultiLineText(signature, n=6))

RT_PATTERN = re.compile(r'(?s){RT}.*?{(.+?)}.*?{/RT}')
RT_OPEN_PATTERN = re.compile(r'{RT}')
RT_CLOSE_PATTERN = re.compile(r'{/RT}')
RT_STRIP_PATTERN = re.compile(r'(?s){RT}.*?{/RT}')
RT_TAG_REPLACE_PATTERN = re.compile(r'{(.*?)}')

def _processTags(tagReplacements, message):
  while True:
    match = RT_PATTERN.search(message)
    if not match:
      break
    if tagReplacements.get(match.group(1)):
      message = RT_OPEN_PATTERN.sub(u'', message, count=1)
      message = RT_CLOSE_PATTERN.sub(u'', message, count=1)
    else:
      message = RT_STRIP_PATTERN.sub(u'', message, count=1)
  while True:
    match = RT_TAG_REPLACE_PATTERN.search(message)
    if not match:
      break
    message = re.sub(match.group(0), tagReplacements.get(match.group(1), u''), message)
  return message

def _processSignature(tagReplacements, signature, html):
  if signature:
    signature = signature.replace(u'\r', u'').replace(u'\\n', u'<br/>')
    if tagReplacements:
      signature = _processTags(tagReplacements, signature)
    if not html:
      signature = signature.replace(u'\n', u'<br/>')
  return signature

def getSendAsAttributes(myarg, body, tagReplacements):
  if myarg == u'replace':
    matchTag = getString(OB_TAG)
    matchReplacement = getString(OB_STRING, minLen=0)
    tagReplacements[matchTag] = matchReplacement
  elif myarg == u'name':
    body[u'displayName'] = getString(OB_NAME, minLen=0)
  elif myarg == u'replyto':
    body[u'replyToAddress'] = getEmailAddress(noUid=True)
  elif myarg == u'default':
    body[u'isDefault'] = True
  elif myarg == u'treatasalias':
    body[u'treatAsAlias'] = getBoolean()
  else:
    unknownArgumentExit()

def addUpdateSendAs(users, addCmd):
  emailAddress = getEmailAddress(noUid=True)
  if addCmd:
    body = {u'sendAsEmail': emailAddress, u'displayName': getString(OB_NAME)}
  else:
    body = {}
  signature = None
  tagReplacements = {}
  html = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg in [u'signature', u'sig']:
      if checkArgumentPresent(FILE_ARGUMENT):
        filename = getString(OB_FILE_NAME)
        encoding = getCharSet()
        signature = readFile(filename, encoding=encoding)
      else:
        signature = getString(OB_STRING, minLen=0)
    elif myarg == u'html':
      html = True
    else:
      getSendAsAttributes(myarg, body, tagReplacements)
  if signature is not None:
    body[u'signature'] = _processSignature(tagReplacements, signature, html)
  kwargs = {u'body': body}
  if not addCmd:
    kwargs[u'sendAsEmail'] = emailAddress
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    print u'User: {0}, {1} SendAs Address: {2}{3}'.format(user, [u'Update', u'Add'][addCmd], emailAddress, currentCount(i, count))
    callGAPI(gmail.users().settings().sendAs(), [u'patch', u'create'][addCmd],
             soft_errors=True,
             userId=u'me', **kwargs)

def deleteSendAs(users):
  emailAddress = getEmailAddress()
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    print u'User: {0}, Delete SendAs Address: {1}{2}'.format(user, emailAddress, currentCount(i, count))
    callGAPI(gmail.users().settings().sendAs(), u'delete',
             soft_errors=True,
             userId=u'me', sendAsEmail=emailAddress)

def infoSendAs(users):
  emailAddress = getEmailAddress()
  formatSig = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'format':
      formatSig = True
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    print u'User: {0}, Show SendAs Address:{1}'.format(user, currentCount(i, count))
    result = callGAPI(gmail.users().settings().sendAs(), u'get',
                      soft_errors=True,
                      userId=u'me', sendAsEmail=emailAddress)
    if result:
      _showSendAs(result, i, count, formatSig)

def printShowSendAs(users, csvFormat):
  if csvFormat:
    todrive = False
    titles = [u'User', u'displayName', u'sendAsEmail', u'replyToAddress', u'isPrimary', u'isDefault', u'treatAsAlias', u'verificationStatus']
    csvRows = []
  formatSig = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if csvFormat and myarg == u'todrive':
      todrive = True
    elif not csvFormat and myarg == u'format':
      formatSig = True
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    result = callGAPI(gmail.users().settings().sendAs(), u'list',
                      soft_errors=True,
                      userId=u'me')
    jcount = len(result.get(u'sendAs', [])) if (result) else 0
    if not csvFormat:
      print u'User: {0}, SendAs Addresses:{1}'.format(user, currentCount(i, count))
      if jcount == 0:
        continue
      j = 0
      for sendas in result[u'sendAs']:
        j += 1
        _showSendAs(sendas, j, jcount, formatSig)
    else:
      if jcount == 0:
        continue
      for sendas in result[u'sendAs']:
        row = {u'User': user, u'isPrimary': False}
        for item in sendas:
          if item not in titles:
            titles.append(item)
          row[item] = sendas[item]
        csvRows.append(row)
  if csvFormat:
    writeCSVfile(csvRows, titles, u'SendAs', todrive)

def setShortCuts(users):
  emailSettings = getEmailSettingsObject()
  enable = getBoolean()
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, userName, emailSettings.domain = splitEmailAddressOrUID(user)
    print u"Setting Keyboard Short Cuts to %s for %s%s" % (str(enable), user, currentCount(i, count))
    callGData(emailSettings, u'UpdateGeneral', soft_errors=True, username=userName, shortcuts=enable)

def setSignature(users):
  tagReplacements = {}
  if checkArgumentPresent(FILE_ARGUMENT):
    filename = getString(OB_FILE_NAME)
    encoding = getCharSet()
    signature = readFile(filename, encoding=encoding)
  else:
    signature = getString(OB_STRING, minLen=0)
  body = {}
  html = primary = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'primary':
      primary = True
    elif myarg == u'html':
      html = True
    else:
      getSendAsAttributes(myarg, body, tagReplacements)
  body[u'signature'] = _processSignature(tagReplacements, signature, html)
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    print u'User: {0}, Set Signature{1}'.format(user, currentCount(i, count))
    if primary:
      result = callGAPI(gmail.users().settings().sendAs(), u'list',
                        soft_errors=True,
                        userId=u'me')
      if result:
        for sendas in result[u'sendAs']:
          if sendas.get(u'isPrimary', False):
            emailAddress = sendas[u'sendAsEmail']
            callGAPI(gmail.users().settings().sendAs(), u'patch',
                     soft_errors=True,
                     userId=u'me', body=body, sendAsEmail=emailAddress)
            break
    else:
      callGAPI(gmail.users().settings().sendAs(), u'patch',
               soft_errors=True,
               userId=u'me', body=body, sendAsEmail=user)

def showSignature(users):
  formatSig = primary = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'primary':
      primary = True
    elif myarg == u'format':
      formatSig = True
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    if primary:
      result = callGAPI(gmail.users().settings().sendAs(), u'list',
                        soft_errors=True,
                        userId=u'me')
      if result:
        print u'User: {0}, Signature:{1}'.format(user, currentCount(i, count))
        for sendas in result[u'sendAs']:
          if sendas.get(u'isPrimary', False):
            _showSendAs(sendas, 0, 0, formatSig)
            break
    else:
      result = callGAPI(gmail.users().settings().sendAs(), u'get',
                        soft_errors=True,
                        userId=u'me', sendAsEmail=user)
      if result:
        print u'User: {0}, Signature:{1}'.format(user, currentCount(i, count))
        _showSendAs(result, 0, 0, formatSig)

def setSnippets(users):
  emailSettings = getEmailSettingsObject()
  enable = getBoolean()
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, userName, emailSettings.domain = splitEmailAddressOrUID(user)
    print u"Setting Preview Snippets to %s for %s%s" % (str(enable), user, currentCount(i, count))
    callGData(emailSettings, u'UpdateGeneral', soft_errors=True, username=userName, snippets=enable)

def setUnicode(users):
  emailSettings = getEmailSettingsObject()
  enable = getBoolean()
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, userName, emailSettings.domain = splitEmailAddressOrUID(user)
    print u"Setting UTF-8 to %s for %s%s" % (str(enable), user, currentCount(i, count))
    callGData(emailSettings, u'UpdateGeneral', soft_errors=True, username=userName, unicode=enable)

def setVacation(users):
  enable = getBoolean()
  body = {u'enableAutoReply': enable}
  if enable:
    responseBodyType = u'responseBodyPlainText'
    message = None
    tagReplacements = {}
    while CL_argvI < CL_argvLen:
      myarg = getArgument()
      if myarg == u'subject':
        body[u'responseSubject'] = getString(OB_STRING, checkBlank=True)
      elif myarg == u'message':
        message = getString(OB_STRING, checkBlank=True)
      elif myarg == u'file':
        filename = getString(OB_FILE_NAME)
        encoding = getCharSet()
        message = readFile(filename, encoding=encoding)
      elif myarg == u'replace':
        matchTag = getString(OB_TAG)
        matchReplacement = getString(OB_STRING, minLen=0)
        tagReplacements[matchTag] = matchReplacement
      elif myarg == u'html':
        responseBodyType = u'responseBodyHtml'
      elif myarg == u'contactsonly':
        body[u'restrictToContacts'] = True
      elif myarg == u'domainonly':
        body[u'restrictToDomain'] = True
      elif myarg == u'startdate':
        body[u'startTime'] = getYYYYMMDD(returnTimeStamp=True)
      elif myarg == u'enddate':
        body[u'endTime'] = getYYYYMMDD(returnTimeStamp=True)
      else:
        unknownArgumentExit()
    if message:
      if responseBodyType == u'responseBodyHtml':
        message = message.replace(u'\r', u'').replace(u'\\n', u'<br/>')
      else:
        message = message.replace(u'\r', u'').replace(u'\\n', u'\n')
      if tagReplacements:
        message = _processTags(tagReplacements, message)
      body[responseBodyType] = message
    if not message and not body.get(u'responseSubject'):
      missingArgumentExit(u'message or subject')
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    print u"Setting Vacation for %s%s" % (user, currentCount(i, count))
    callGAPI(gmail.users().settings(), u'updateVacation',
             soft_errors=True,
             userId=u'me', body=body)

def showVacation(users):
  formatReply = False
  while CL_argvI < CL_argvLen:
    myarg = getArgument()
    if myarg == u'format':
      formatReply = True
    else:
      unknownArgumentExit()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, gmail = buildGmailGAPIObject(user)
    if not gmail:
      continue
    result = callGAPI(gmail.users().settings(), u'getVacation',
                      soft_errors=True,
                      userId=u'me')
    if result:
      enabled = result[u'enableAutoReply']
      print u'User: {0}, Vacation:{1}'.format(user, currentCount(i, count))
      print u'  Enabled: {0}'.format(enabled)
      if enabled:
        print u'  Contacts Only: {0}'.format(result[u'restrictToContacts'])
        print u'  Domain Only: {0}'.format(result[u'restrictToDomain'])
        if u'startTime' in result:
          print u'  Start Date: {0}'.format(datetime.datetime.fromtimestamp(int(result[u'startTime'])/1000).strftime('%Y-%m-%d'))
        else:
          print u'  Start Date: Started'
        if u'endTime' in result:
          print u'  End Date: {0}'.format(datetime.datetime.fromtimestamp(int(result[u'endTime'])/1000).strftime('%Y-%m-%d'))
        else:
          print u'  End Date: Not specified'
        print convertUTF8(u'  Subject: {0}'.format(result.get(u'responseSubject', u'None')))
        sys.stdout.write(u'  Message:\n   ')
        if result.get(u'responseBodyPlainText'):
          print convertUTF8(indentMultiLineText(result[u'responseBodyPlainText'], n=4))
        elif result.get(u'responseBodyHtml'):
          if formatReply:
            print convertUTF8(indentMultiLineText(dehtml(result[u'responseBodyHtml']), n=4))
          else:
            print convertUTF8(indentMultiLineText(result[u'responseBodyHtml'], n=4))
        else:
          print u'None'

def setWebClips(users):
  emailSettings = getEmailSettingsObject()
  enable = getBoolean()
  checkForExtraneousArguments()
  i = 0
  count = len(users)
  for user in users:
    i += 1
    user, userName, emailSettings.domain = splitEmailAddressOrUID(user)
    print u"Turning Web Clips %s for %s%s" % (enable, user, currentCount(i, count))
    callGData(emailSettings, u'UpdateWebClipSettings', soft_errors=True, username=userName, enable=enable)

def resetDefaultEncodingToUTF8():
  if sys.getdefaultencoding().upper() != u'UTF-8':
    reload(sys)
    if hasattr(sys, u'setdefaultencoding'):
      sys.setdefaultencoding(u'UTF-8')

def ProcessGAMCommandNoQueue(args):
  resetDefaultEncodingToUTF8()
  ProcessGAMCommand(args)

# Process GAM command
def ProcessGAMCommand(args):
  setSysExitRC(0)
  initializeArguments(args)
  try:
    if not SetGlobalVariables():
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if CL_argvI == CL_argvLen:
      showUsage()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    command = getArgument()
    if command == u'batch':
      doBatch()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'csv':
      doCSV()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'version':
      doVersion()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'create':
      argument = getArgument()
      if argument == u'user':
        doCreateUser()
      elif argument == u'group':
        doCreateGroup()
      elif argument in [u'nickname', u'alias']:
        doCreateAlias()
      elif argument in [u'org', u'ou']:
        doCreateOrg()
      elif argument == u'resource':
        doCreateResourceCalendar()
      elif argument in [u'verify', u'verification']:
        doCreateSiteVerification()
      elif argument == u'schema':
        doCreateOrUpdateUserSchema(False)
      elif argument in [u'course', u'class']:
        doCreateCourse()
      elif argument in [u'transfer', u'datatransfer']:
        doCreateDataTranfer()
      elif argument == u'domain':
        doCreateDomain()
      elif argument in [u'domainalias', u'aliasdomain']:
        doCreateDomainAlias()
      elif argument == u'admin':
        doCreateAdmin()
      elif argument in [u'guardianinvite', u'inviteguardian', u'guardian']:
        doInviteGuardian()
      elif argument in [u'project', u'apiproject']:
        doCreateProject()
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'update':
      argument = getArgument()
      if argument == u'user':
        doUpdateUser(getStringReturnInList(OB_EMAIL_ADDRESS))
      elif argument == u'group':
        doUpdateGroup()
      elif argument in [u'nickname', u'alias']:
        doUpdateAlias()
      elif argument in [u'ou', u'org']:
        doUpdateOrg()
      elif argument == u'resource':
        doUpdateResourceCalendar()
      elif argument == u'instance':
        doUpdateInstance()
      elif argument == u'cros':
        doUpdateCrosDevice()
      elif argument == u'mobile':
        doUpdateMobileDevice()
      elif argument in [u'notification', u'notifications']:
        doUpdateNotification()
      elif argument in [u'verify', u'verification']:
        updateSiteVerification()
      elif argument in [u'schema', u'schemas']:
        doCreateOrUpdateUserSchema(True)
      elif argument in [u'course', u'class']:
        doUpdateCourse()
      elif argument in [u'printer', u'print']:
        doUpdatePrinter()
      elif argument == u'domain':
        doUpdateDomain()
      elif argument == u'customer':
        doUpdateCustomer()
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'info':
      argument = getArgument()
      if argument == u'user':
        doInfoUser()
      elif argument == u'group':
        doInfoGroup()
      elif argument in [u'nickname', u'alias']:
        doInfoAlias()
      elif argument == u'instance':
        doInfoInstance()
      elif argument in [u'org', u'ou']:
        doInfoOrg()
      elif argument == u'resource':
        doInfoResourceCalendar()
      elif argument == u'cros':
        doInfoCrosDevice()
      elif argument == u'mobile':
        doInfoMobileDevice()
      elif argument in [u'notifications', u'notification']:
        doInfoNotifications()
      elif argument in [u'verify', u'verification']:
        doInfoSiteVerification()
      elif argument in [u'schema', u'schemas']:
        doInfoUserSchema()
      elif argument in [u'course', u'class']:
        doInfoCourse()
      elif argument in [u'printer', u'print']:
        doInfoPrinter()
      elif argument in [u'transfer', u'datatransfer']:
        doInfoDataTransfer()
      elif argument == u'customer':
        doInfoCustomer()
      elif argument == u'domain':
        doInfoDomain()
      elif argument in [u'domainalias', u'aliasdomain']:
        doInfoDomainAlias()
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'cancel':
      argument = getArgument()
      if argument in [u'guardianinvitation', u'guardianinvitations']:
        doCancelGuardianInvitation()
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'delete':
      argument = getArgument()
      if argument == u'user':
        doDeleteUser()
      elif argument == u'group':
        doDeleteGroup()
      elif argument in [u'nickname', u'alias']:
        doDeleteAlias()
      elif argument == u'org':
        doDeleteOrg()
      elif argument == u'resource':
        doDeleteResourceCalendar()
      elif argument == u'mobile':
        doDeleteMobileDevice()
      elif argument in [u'notification', u'notifications']:
        doDeleteNotification()
      elif argument in [u'schema', u'schemas']:
        doDeleteUserSchema()
      elif argument in [u'course', u'class']:
        doDeleteCourse()
      elif argument in [u'printer', u'printers']:
        doDeletePrinter()
      elif argument == u'domain':
        doDeleteDomain()
      elif argument in [u'domainalias', u'aliasdomain']:
        doDeleteDomainAlias()
      elif argument == u'admin':
        doDeleteAdmin()
      elif argument in [u'guardian', u'guardians']:
        doDeleteGuardian()
      elif argument in [u'project', u'projects']:
        doDeleteProjects()
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'undelete':
      argument = getArgument()
      if argument == u'user':
        doUndeleteUser()
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'audit':
      argument = getArgument()
      if argument == u'monitor':
        auditWhat = getArgument()
        if auditWhat == u'create':
          doCreateMonitor()
        elif auditWhat == u'list':
          doShowMonitors()
        elif auditWhat == u'delete':
          doDeleteMonitor()
        else:
          unknownArgumentExit()
      elif argument == u'activity':
        auditWhat = getArgument()
        if auditWhat == u'request':
          doSubmitActivityRequest()
        elif auditWhat == u'status':
          doStatusActivityRequests()
        elif auditWhat == u'download':
          doDownloadActivityRequest()
        elif auditWhat == u'delete':
          doDeleteActivityRequest()
        else:
          unknownArgumentExit()
      elif argument == u'export':
        auditWhat = getArgument()
        if auditWhat == u'status':
          doStatusExportRequests()
        elif auditWhat == u'watch':
          doWatchExportRequest()
        elif auditWhat == u'download':
          doDownloadExportRequest()
        elif auditWhat == u'request':
          doSubmitRequestExport()
        elif auditWhat == u'delete':
          doDeleteExportRequest()
        else:
          unknownArgumentExit()
      elif argument == u'uploadkey':
        doUploadAuditKey()
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'print':
      argument = getArgument().replace(u'-', u'')
      if argument == u'users':
        doPrintUsers()
      elif argument in [u'nicknames', u'aliases']:
        doPrintAliases()
      elif argument == u'groups':
        doPrintGroups()
      elif argument in [u'groupmembers', u'groupsmembers']:
        doPrintGroupMembers()
      elif argument in [u'orgs', u'ous']:
        doPrintOrgs()
      elif argument == u'resources':
        doPrintResourceCalendars()
      elif argument == u'cros':
        doPrintCrosDevices()
      elif argument == u'mobile':
        doPrintMobileDevices()
      elif argument in [u'license', u'licenses', u'licence', u'licences']:
        doPrintLicenses()
      elif argument in [u'token', u'tokens', u'oauth', u'3lo']:
        printShowTokens(None, None, True)
      elif argument in [u'schema', u'schemas']:
        doPrintShowUserSchemas(True)
      elif argument in [u'courses', u'classes']:
        doPrintCourses()
      elif argument in [u'courseparticipants', u'classparticipants']:
        doPrintCourseParticipants()
      elif argument == u'printers':
        doPrintPrinters()
      elif argument == u'printjobs':
        doPrintPrintJobs()
      elif argument in [u'transfers', u'datatransfers']:
        doPrintDataTransfers()
      elif argument == u'transferapps':
        doPrintTransferApps()
      elif argument == u'domains':
        doPrintDomains()
      elif argument in [u'domainaliases', u'aliasdomains']:
        doPrintDomainAliases()
      elif argument == u'admins':
        doPrintAdmins()
      elif argument in [u'roles', u'adminroles']:
        doPrintAdminRoles()
      elif argument in [u'guardian', u'guardians']:
        doPrintShowGuardians(True)
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'show':
      argument = getArgument()
      if argument in [u'schema', u'schemas']:
        doPrintShowUserSchemas(False)
      elif argument in [u'guardian', u'guardians']:
        doPrintShowGuardians(False)
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command in [u'oauth', u'oauth2']:
      argument = getArgument()
      if argument in [u'request', u'create']:
        doOAuthRequest(getEmailAddress(noUid=True, optional=True))
      elif argument in [u'info', u'verify']:
        doOAuthInfo()
      elif argument in [u'delete', u'revoke']:
        doOAuthDelete()
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'calendar':
      cal = buildGAPIObject(u'calendar')
      calendarId = getEmailAddress()
      argument = getArgument()
      if argument == u'showacl':
        doCalendarShowACL(cal, calendarId)
      elif argument == u'add':
        doCalendarAddACL(cal, calendarId)
      elif argument in [u'del', u'delete']:
        doCalendarDeleteACL(cal, calendarId)
      elif argument == u'update':
        doCalendarUpdateACL(cal, calendarId)
      elif argument == u'wipe':
        doCalendarWipeEvents(cal, calendarId)
      elif argument == u'addevent':
        doCalendarAddEvent(cal, calendarId)
      elif argument == u'deleteevent':
        doCalendarDeleteEvent(cal, calendarId)
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'printer':
      printerId = getString(OB_PRINTER_ID)
      if printerId.lower() == u'register':
        doPrinterRegister()
      else:
        argument = getArgument()
        if argument == u'showacl':
          doPrinterShowACL(printerId)
        elif argument == u'add':
          doPrinterAddACL(printerId)
        elif argument in [u'del', u'delete', u'remove']:
          doPrinterDeleteACL(printerId)
        else:
          unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'printjob':
      jobPrinterId = getString(OB_JOB_OR_PRINTER_ID)
      argument = getArgument()
      if argument == u'delete':
        doPrintJobDelete(jobPrinterId)
      elif argument == u'cancel':
        doPrintJobCancel(jobPrinterId)
      elif argument == u'submit':
        doPrintJobSubmit(jobPrinterId)
      elif argument == u'fetch':
        doPrintJobFetch(jobPrinterId)
      elif argument == u'resubmit':
        doPrintJobResubmit(jobPrinterId)
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'report':
      showReport()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'whatis':
      doWhatIs()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command in [u'course', u'class']:
      courseId = getCourseId()
      argument = getArgument()
      if argument in [u'add', u'create']:
        doCourseAddParticipant(courseId)
      elif argument in [u'del', u'delete', u'remove']:
        doCourseRemoveParticipant(courseId)
      elif argument == u'sync':
        doCourseSyncParticipants(courseId)
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    putArgumentBack()
    users = getUsersToModify(getChoice(usergroup_types), getString(OB_ENTITY))
    command = getArgument()
    if command == u'print' and CL_argvI == CL_argvLen:
      for user in users:
        print user
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'show':
      showWhat = getArgument()
      if showWhat in [u'labels', u'label']:
        showLabels(users)
      elif showWhat == u'profile':
        showProfile(users)
      elif showWhat == u'calendars':
        printShowCalendars(users, False)
      elif showWhat == u'calsettings':
        showCalSettings(users)
      elif showWhat == u'drivesettings':
        printDriveSettings(users)
      elif showWhat == u'drivefileacl':
        showDriveFileACL(users)
      elif showWhat == u'filelist':
        printDriveFileList(users)
      elif showWhat == u'filetree':
        showDriveFileTree(users)
      elif showWhat == u'fileinfo':
        showDriveFileInfo(users)
      elif showWhat == u'filepath':
        showDriveFilePath(users)
      elif showWhat == u'filerevisions':
        showDriveFileRevisions(users)
      elif showWhat == u'sendas':
        printShowSendAs(users, False)
      elif showWhat == u'gmailprofile':
        printShowGmailProfile(users, False)
      elif showWhat == u'gplusprofile':
        printShowGplusProfile(users, False)
      elif showWhat in [u'sig', u'signature']:
        showSignature(users)
      elif showWhat == u'forward':
        printShowForward(users, False)
      elif showWhat in [u'pop', u'pop3']:
        showPop(users)
      elif showWhat in [u'imap', u'imap4']:
        showImap(users)
      elif showWhat == u'vacation':
        showVacation(users)
      elif showWhat in [u'delegate', u'delegates']:
        printShowDelegates(users, False)
      elif showWhat in [u'backupcode', u'backupcodes', u'verificationcodes']:
        showBackupCodes(users)
      elif showWhat in [u'asp', u'asps', u'applicationspecificpasswords']:
        showASPs(users)
      elif showWhat in [u'token', u'tokens', u'oauth', u'3lo']:
        printShowTokens(u'users', users, False)
      elif showWhat == u'driveactivity':
        printDriveActivity(users)
      elif showWhat in [u'filter', u'filters']:
        printShowFilters(users, False)
      elif showWhat in [u'forwardingaddress', u'forwardingaddresses']:
        printShowForwardingAddresses(users, False)
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    elif command == u'print':
      printWhat = getArgument()
      if printWhat == u'calendars':
        printShowCalendars(users, True)
      elif printWhat in [u'delegate', u'delegates']:
        printShowDelegates(users, True)
      elif printWhat == u'driveactivity':
        printDriveActivity(users)
      elif printWhat == u'drivesettings':
        printDriveSettings(users)
      elif printWhat == u'filelist':
        printDriveFileList(users)
      elif printWhat in [u'filter', u'filters']:
        printShowFilters(users, True)
      elif printWhat == u'forward':
        printShowForward(users, True)
      elif printWhat in [u'forwardingaddress', u'forwardingaddresses']:
        printShowForwardingAddresses(users, True)
      elif printWhat == u'sendas':
        printShowSendAs(users, True)
      elif printWhat == u'gmailprofile':
        printShowGmailProfile(users, True)
      elif printWhat == u'gplusprofile':
        printShowGplusProfile(users, True)
      elif printWhat in [u'token', u'tokens', u'oauth', u'3lo']:
        printShowTokens(u'users', users, True)
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    elif command == u'info':
      infoWhat = getArgument()
      if infoWhat == u'calendar':
        infoCalendar(users)
      elif infoWhat in [u'filter', u'filters']:
        infoFilters(users)
      elif infoWhat in [u'forwardingaddress', u'forwardingaddresses']:
        infoForwardingAddresses(users)
      elif infoWhat == u'sendas':
        infoSendAs(users)
      else:
        unknownArgumentExit()
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if (GC_Values[GC_AUTO_BATCH_MIN] > 0) and (len(users) > GC_Values[GC_AUTO_BATCH_MIN]):
      run_batch([[u'gam', u'user', user]+CL_argv[CL_argvI-1:] for user in users])
      sys.exit(GM_Globals[GM_SYSEXITRC])
    if command == u'transfer':
      transferWhat = getArgument()
      if transferWhat == u'drive':
        transferDriveFiles(users)
      elif transferWhat == u'seccals':
        transferSecCals(users)
      else:
        unknownArgumentExit()
    elif command == u'modify':
      modifyWhat = getArgument()
      if modifyWhat in [u'message', u'messages']:
        processMessages(users, u'modify')
      else:
        unknownArgumentExit()
    elif command == u'trash':
      trashWhat = getArgument()
      if trashWhat in [u'message', u'messages']:
        processMessages(users, u'trash')
      else:
        unknownArgumentExit()
    elif command == u'untrash':
      untrashWhat = getArgument()
      if untrashWhat in [u'message', u'messages']:
        processMessages(users, u'untrash')
      else:
        unknownArgumentExit()
    elif command in [u'delete', u'del']:
      delWhat = getArgument()
      if delWhat == u'delegate':
        deleteDelegate(users)
      elif delWhat == u'calendar':
        deleteCalendar(users)
      elif delWhat == u'label':
        deleteLabel(users)
      elif delWhat in [u'message', u'messages']:
        processMessages(users, u'delete')
      elif delWhat == u'photo':
        deletePhoto(users)
      elif delWhat in [u'license', u'licence']:
        processLicense(users, u'delete')
      elif delWhat in [u'backupcode', u'backupcodes', u'verificationcodes']:
        deleteBackupCodes(users)
      elif delWhat in [u'asp', u'asps', u'applicationspecificpasswords']:
        deleteASP(users)
      elif delWhat in [u'token', u'tokens', u'oauth', u'3lo']:
        deleteTokens(users)
      elif delWhat in [u'group', u'groups']:
        deleteUserFromGroups(users)
      elif delWhat in [u'alias', u'aliases']:
        deleteUsersAliases(users)
      elif delWhat == u'emptydrivefolders':
        deleteEmptyDriveFolders(users)
      elif delWhat == u'drivefile':
        deleteDriveFile(users)
      elif delWhat in [u'drivefileacl', u'drivefileacls']:
        deleteDriveFileACL(users)
      elif delWhat in [u'filter', u'filters']:
        deleteFilters(users)
      elif delWhat in [u'forwardingaddress', u'forwardingaddresses']:
        deleteForwardingAddresses(users)
      elif delWhat == u'sendas':
        deleteSendAs(users)
      else:
        unknownArgumentExit()
    elif command == u'add':
      addWhat = getArgument()
      if addWhat == u'calendar':
        addCalendar(users)
      elif addWhat == u'drivefile':
        addDriveFile(users)
      elif addWhat in [u'license', u'licence']:
        processLicense(users, u'insert')
      elif addWhat in [u'drivefileacl', u'drivefileacls']:
        addDriveFileACL(users)
      elif addWhat in [u'label', u'labels']:
        addLabel(users)
      elif addWhat in [u'delegate', u'delegates']:
        addDelegate(users, False)
      elif addWhat in [u'filter', u'filters']:
        addFilter(users)
      elif addWhat in [u'forwardingaddress', u'forwardingaddresses']:
        addForwardingAddresses(users)
      elif addWhat in [u'group', u'groups']:
        addUserToGroups(users)
      elif addWhat == u'sendas':
        addUpdateSendAs(users, True)
      else:
        unknownArgumentExit()
    elif command == u'update':
      updateWhat = getArgument()
      if updateWhat == u'calendar':
        updateCalendar(users)
      elif updateWhat == u'calattendees':
        updateCalendarAttendees(users)
      elif updateWhat == u'photo':
        updatePhoto(users)
      elif updateWhat in [u'license', u'licence']:
        processLicense(users, u'patch')
      elif updateWhat == u'user':
        doUpdateUser(users)
      elif updateWhat in [u'backupcode', u'backupcodes', u'verificationcodes']:
        updateBackupCodes(users)
      elif updateWhat == u'drivefile':
        doUpdateDriveFile(users)
      elif updateWhat in [u'drivefileacls', u'drivefileacl']:
        updateDriveFileACL(users)
      elif updateWhat in [u'label', u'labels']:
        updateLabels(users)
      elif updateWhat == u'labelsettings':
        updateLabelSettings(users)
      elif updateWhat == u'sendas':
        addUpdateSendAs(users, False)
      else:
        unknownArgumentExit()
    elif command in [u'deprov', u'deprovision']:
      deprovisionUser(users)
    elif command == u'get':
      getWhat = getArgument()
      if getWhat == u'photo':
        getPhoto(users)
      elif getWhat == u'drivefile':
        getDriveFile(users)
      else:
        unknownArgumentExit()
    elif command == u'empty':
      emptyWhat = getArgument()
      if emptyWhat == u'drivetrash':
        emptyDriveTrash(users)
      else:
        unknownArgumentExit()
    elif command == u'check':
      checkWhat = sys.argv[4].replace(u'_', '').lower()
      if checkWhat == u'serviceaccount':
        doCheckServiceAccount(users)
      else:
        unknownArgumentExit()
    elif command == u'profile':
      setProfile(users)
    elif command == u'imap':
      setImap(users)
    elif command in [u'pop', u'pop3']:
      setPop(users)
    elif command == u'sendas':
      addUpdateSendAs(users, True)
    elif command == u'language':
      setLanguage(users)
    elif command in [u'utf', u'utf8', u'utf-8', u'unicode']:
      setUnicode(users)
    elif command == u'pagesize':
      setPageSize(users)
    elif command == u'shortcuts':
      setShortCuts(users)
    elif command == u'arrows':
      setArrows(users)
    elif command == u'snippets':
      setSnippets(users)
    elif command == u'label':
      addLabel(users)
    elif command == u'filter':
      addFilter(users)
    elif command == u'forward':
      setForward(users)
    elif command in [u'sig', u'signature']:
      setSignature(users)
    elif command == u'vacation':
      setVacation(users)
    elif command == u'webclips':
      setWebClips(users)
    elif command in [u'delegate', u'delegates']:
      addDelegate(users, True)
    else:
      unknownArgumentExit()
    sys.exit(GM_Globals[GM_SYSEXITRC])
  except KeyboardInterrupt:
    setSysExitRC(50)
  except socket.error as e:
    stderrErrorMsg(e)
    sys.exit()
  except MemoryError:
    stderrErrorMsg(MESSAGE_GAM_OUT_OF_MEMORY)
    sys.exit(99)
  except SystemExit as e:
    GM_Globals[GM_SYSEXITRC] = e.code
  return GM_Globals[GM_SYSEXITRC]

# From: https://github.com/pyinstaller/pyinstaller/wiki/Recipe-Multiprocessing
#
if sys.platform.startswith('win'):
  from multiprocessing import freeze_support
  try:
    import multiprocessing.popen_spawn_win32 as forking
  except ImportError:
    import multiprocessing.forking as forking

  # First define a modified version of Popen.
  class _Popen(forking.Popen):
    def __init__(self, *args, **kw):
      if hasattr(sys, 'frozen'):
        # We have to set original _MEIPASS2 value from sys._MEIPASS
        # to get --onefile mode working.
        os.putenv('_MEIPASS2', sys._MEIPASS)
      try:
        super(_Popen, self).__init__(*args, **kw)
      finally:
        if hasattr(sys, 'frozen'):
          # On some platforms (e.g. AIX) 'os.unsetenv()' is not
          # available. In those cases we cannot delete the variable
          # but only set it to the empty string. The bootloader
          # can handle this case.
          if hasattr(os, 'unsetenv'):
            os.unsetenv('_MEIPASS2')
          else:
            os.putenv('_MEIPASS2', '')

  # Second override 'Popen' class with our modified version.
  forking.Popen = _Popen

  def win32_unicode_argv():
    from ctypes import POINTER, byref, cdll, c_int, windll
    from ctypes.wintypes import LPCWSTR, LPWSTR

    GetCommandLineW = cdll.kernel32.GetCommandLineW
    GetCommandLineW.argtypes = []
    GetCommandLineW.restype = LPCWSTR

    CommandLineToArgvW = windll.shell32.CommandLineToArgvW
    CommandLineToArgvW.argtypes = [LPCWSTR, POINTER(c_int)]
    CommandLineToArgvW.restype = POINTER(LPWSTR)

    cmd = GetCommandLineW()
    argc = c_int(0)
    argv = CommandLineToArgvW(cmd, byref(argc))
    if argc.value > 0:
      # Remove Python executable and commands if present
      argc_value = int(argc.value)
      sys.argv = argv[argc_value-len(sys.argv):argc_value]

# Run from command line
if __name__ == "__main__":
  resetDefaultEncodingToUTF8()
  if sys.platform.startswith('win'):
    freeze_support()
    win32_unicode_argv() # cleanup sys.argv on Windows
  sys.exit(ProcessGAMCommand(sys.argv))

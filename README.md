GAM-N
=====
GAM-N is a free, open source command line tool for Google G Suite Administrators to manage domain and user settings quickly and easily.

Documentation
-------------
General GAM documentation is hosted in the [GitHub Wiki]. Documentation specifically for GAM-N is in Gam*.txt files.

Downloads
---------
You can download the current GAM-N release from the [GitHub Releases] page.

Download - do a or b or c

a) Single Executable, Mac OS - *.xz
- Download the archive, extract the contents into some directory.
- Start a terminal session and cd to the install directory.

b) Single Executable, Windows - *.msi
- Download the installer and run it.
- Start a Command Prompt/PowerShell session and cd to the install directory.

c) Source, all platforms - *.zip, *.gz
- Download the archive, extract the contents into some directory.
- Start a terminal/Command Prompt/PowerShell session and cd to the install directory.

Installation - New Users
------------------------
Enter the following gam commands and follow instructions to create the necessary authorizations.
- Build GAM Project for authorization: ```gam create project```
- Authorize Gam Client: ```gam oauth create```
- Authorize Service Account: ```gam user <admin email address> check serviceaccount```

Installation - Upgrading from a prior version of GAM.
----------------------------------------------------------------------------------
Copy your existing client_secrets.json/oath2.txt/oauth2service.json files to the install directory.

Mailing List / Discussion group
-------------------------------
The GAM mailing list / discussion group is hosted on [Google Groups].  You can join the list and interact via email, or just post from the web itself.

Source Repository
-----------------
The official GAM-N source repository is on [GitHub] in the master branch.

Author
------
GAM-N is maintained by <a href="mailto:ross.scroggs@gmail.com">Ross Scroggs</a>.

[GitHub Releases]: https://github.com/taers232c/GAM-N/releases
[GitHub]: https://github.com/taers232c/GAM-N/tree/master
[GitHub Wiki]: https://github.com/jay0lee/GAM/wiki/
[Google Groups]: http://groups.google.com/group/google-apps-manager

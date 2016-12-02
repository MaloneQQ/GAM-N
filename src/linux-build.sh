rm -rf gam
rm -rf build
rm -rf  dist
rm -rf gam-n-$1-linux-$(arch).tar.xz

export LD_LIBRARY_PATH=/usr/local/lib
pyinstaller --clean -F --distpath=gam linux-gam.spec
cp LICENSE gam
cp license.rtf gam
cp whatsnew.txt gam
cp Gam*.txt gam

tar cfJ gam-n-$1-linux-$(arch).tar.xz gam/ 

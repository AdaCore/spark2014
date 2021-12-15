IRONSIDES compilation instructions

SPARK (http://www.altran-praxis.com/spark.aspx) is a programming language that uses formal methods to prove software properties.  There are two separate compilation processes:

1) Use the SPARK toolset (http://libre.adacore.com/tools/spark-gpl-edition/) to perform the automatic theorem proving on the code.  (If you haven't modified the distribution, this step is not required as it has already been done by the authors-- you do still have to download SPARK to get the library modules).

2) Use an Ada compiler (e.g. http://libre.adacore.com/tools/gnat-gpl-edition/) to create an executable.

=============================WINDOWS DIRECTIONS===========================
Download and install GNAT, SPARK

The following command line will create an executable (assuming SPARK is installed to c:\spark\2012).

gnatmake -gnat05 -O3 -gnatp -Ic:\spark\2012\lib\spark -Ic:\spark\2012\lib\spark\current spark_dns_main

=============================LINUX DIRECTIONS===========================
download, e.g., gnat-gpl-2012-x86_64-pc-linux-gnu-bin.tar.gz and spark-gpl-2012-x86_64-pc-linux-gnu.tar.gz
Do NOT use the GNAT you can apt-get on Debian (last I checked it had a bug)

gzip -d *.gz
tar xpf *.tar
make sure you have a C compiler installed (e.g. on Ubuntu, apt-get install build-essential)

cd gnat-2012-x86_64-pc-linux-gnu-bin
sudo ./doinstall

cd ../
# you'll need to change the paths below to yours
export LIBRARY_PATH=/usr/lib/x86_64-linux-gnu
export PATH=/usr/gnat/bin:$PATH
gnatmake -gnat05 -O3 -gnatp -I/home/student/sparkgpl/lib/spark -I/home/student/sparkgpl/lib/spark/current spark_dns_main

Now run it with (e.g.):
dos2unix dfcs.usafa.edu.zonefile
sudo ./spark_dns_main dfcs.usafa.edu.zonefile

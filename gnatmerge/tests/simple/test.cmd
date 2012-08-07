gnatmerge -e driver.py -Pcontracts > tmp.out
diff -u test.out tmp.out

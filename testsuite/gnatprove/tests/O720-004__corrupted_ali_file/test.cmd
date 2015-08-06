gnatprove -P test.gpr -f -q

head -n -4 gnatprove/test.ali > gnatprove/tmp.ali
rm gnatprove/test.ali
mv gnatprove/tmp.ali gnatprove/test.ali

gnatprove -P test.gpr -q

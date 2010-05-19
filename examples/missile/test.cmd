gnatmake -q -c -gnatcC -Pharness
codepeer -all -lib test.lib -global -quiet -background
codepeer_msg_reader test.output | grep -v 'a-.*\.ad[sb]' | tr -d '\r' > test.out.new
diff -u test.out.expected test.out.new

with Test_08_Util;

package Test_08 with Elaborate_Body is

   type T1 is private;
   type T2 is private;
   type T3 is private;

private

   type T1 is record
      N : Integer := 42;
   end record
   with Type_Invariant => Test_08_Util.Is_Positive_Good (T1.N) or T1.N = -5;
   --  Should be OK

   type T2 is record
      N : Integer := 42;
   end record
   with Type_Invariant => Test_08_Util.Is_Positive_Bad (T2.N) or T2.N = -5;
   --  Self-recursive

   type T3 is record
      N : Integer := 42;
   end record
   with Type_Invariant => Test_08_Util.Is_Positive_Ugly (T3.N) or T3.N = -5;
   --  Calls invariant for T1 (ugly) but otherwise OK

end Test_08;

with AUnit.Assertions; use AUnit.Assertions;

package body Pack.Test_Data.Tests is

   function Wrap_Test_P1_087c71_fe3908 (X : Integer)  return Integer
   is
   begin
      AUnit.Assertions.Assert
        (((X <= Integer'Last - 1)) and (X < 16),
         "req_sloc(/cognac.a/users/guitton/GIT/HILITE/hi-lite/gnatmerge/tests/simple/src/pack.ads:13):test case 1 precondition violated");
      declare
         Test_P1_087c71_fe3908_Result : constant Integer := GNATtest_Generated.GNATtest_Standard.Pack.P1 (X);
      begin
         AUnit.Assertions.Assert
           (((Test_P1_087c71_fe3908_Result = X + 1)) and (Test_P1_087c71_fe3908_Result < 4),
            "ens_sloc(/cognac.a/users/guitton/GIT/HILITE/hi-lite/gnatmerge/tests/simple/src/pack.ads:14:):test case 1 postcondition violated");
         return Test_P1_087c71_fe3908_Result;
      end;
   end Wrap_Test_P1_087c71_fe3908;
   procedure Test_P1_087c71_fe3908 (Gnattest_T : in out Test) is separate;
   --  pack.ads:10:4:P1:test case 1

   function Wrap_Test_P2_7727fe_cdf8e0 (X : Integer)  return Integer
   is
   begin
      AUnit.Assertions.Assert
        (X < 16,
         "req_sloc(/cognac.a/users/guitton/GIT/HILITE/hi-lite/gnatmerge/tests/simple/src/pack.ads:23):test case 2 precondition violated");
      declare
         Test_P2_7727fe_cdf8e0_Result : constant Integer := GNATtest_Generated.GNATtest_Standard.Pack.P2 (X);
      begin
         AUnit.Assertions.Assert
           (Test_P2_7727fe_cdf8e0_Result < 4,
            "ens_sloc(/cognac.a/users/guitton/GIT/HILITE/hi-lite/gnatmerge/tests/simple/src/pack.ads:24:):test case 2 postcondition violated");
         return Test_P2_7727fe_cdf8e0_Result;
      end;
   end Wrap_Test_P2_7727fe_cdf8e0;
   procedure Test_P2_7727fe_cdf8e0 (Gnattest_T : in out Test) is separate;
   --  pack.ads:20:4:P2:test case 2

   function Wrap_Test_P3_72ef10_519ea0 (X : Integer)  return Integer
   is
   begin
      AUnit.Assertions.Assert
        (((X <= Integer'Last - 1)) and (X < 16),
         "req_sloc(/cognac.a/users/guitton/GIT/HILITE/hi-lite/gnatmerge/tests/simple/src/pack.ads:33):test case 3 precondition violated");
      declare
         Test_P3_72ef10_519ea0_Result : constant Integer := GNATtest_Generated.GNATtest_Standard.Pack.P3 (X);
      begin
         AUnit.Assertions.Assert
           (((Test_P3_72ef10_519ea0_Result = X + 5)) and (Test_P3_72ef10_519ea0_Result < 4),
            "ens_sloc(/cognac.a/users/guitton/GIT/HILITE/hi-lite/gnatmerge/tests/simple/src/pack.ads:34:):test case 3 postcondition violated");
         return Test_P3_72ef10_519ea0_Result;
      end;
   end Wrap_Test_P3_72ef10_519ea0;
   procedure Test_P3_72ef10_519ea0 (Gnattest_T : in out Test) is separate;
   --  pack.ads:30:4:P3:test case 3

   function Wrap_Test_P4_0599a5_76a6c4 (X : Integer)  return Integer
   is
   begin
      AUnit.Assertions.Assert
        (X < 16,
         "req_sloc(/cognac.a/users/guitton/GIT/HILITE/hi-lite/gnatmerge/tests/simple/src/pack.ads:43):test case 4 precondition violated");
      declare
         Test_P4_0599a5_76a6c4_Result : constant Integer := GNATtest_Generated.GNATtest_Standard.Pack.P4 (X);
      begin
         AUnit.Assertions.Assert
           (Test_P4_0599a5_76a6c4_Result <= 4,
            "ens_sloc(/cognac.a/users/guitton/GIT/HILITE/hi-lite/gnatmerge/tests/simple/src/pack.ads:44:):test case 4 postcondition violated");
         return Test_P4_0599a5_76a6c4_Result;
      end;
   end Wrap_Test_P4_0599a5_76a6c4;
   procedure Test_P4_0599a5_76a6c4 (Gnattest_T : in out Test) is separate;
   --  pack.ads:40:4:P4:test case 4

   procedure Test_P5_c00802 (Gnattest_T : in out Test) is separate;
   --  pack.ads:50:4:P5

   procedure Test_P6_0371df (Gnattest_T : in out Test) is separate;
   --  pack.ads:60:4:P6

end Pack.Test_Data.Tests;

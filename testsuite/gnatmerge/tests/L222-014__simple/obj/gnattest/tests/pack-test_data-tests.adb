with AUnit.Assertions; use AUnit.Assertions;

package body Pack.Test_Data.Tests is

   function Wrap_Test_P1_087c71_fe3908 (X : Integer)  return Integer
   is
   begin
      AUnit.Assertions.Assert
        (((X <= Integer'Last - 1)) and (X < 16),
         "req_sloc(pack.ads:13):test case 1 precondition violated");
      declare
         Test_P1_087c71_fe3908_Result : constant Integer := GNATtest_Generated.GNATtest_Standard.Pack.P1 (X);
      begin
         AUnit.Assertions.Assert
           (((Test_P1_087c71_fe3908_Result = X + 1)) and (Test_P1_087c71_fe3908_Result < 4),
            "ens_sloc(pack.ads:14:):test case 1 postcondition violated");
         return Test_P1_087c71_fe3908_Result;
      end;
   end Wrap_Test_P1_087c71_fe3908;
--  GNATtest marker section
--  PLEASE DO NOT MODIFY OR REMOVE THIS SECTION
--  test routine beginning
--  hash: 087c719339b1acad285396509c2ab99e3a1f9dbf
--  test case hash: fe3908fff57c5e255fe3b0776fa3394e042215cc
--  hash version: 1
--  end of GNATtest marker section

   procedure Test_P1_087c71_fe3908 (Gnattest_T : in out Test) is
      pragma Unreferenced (Gnattest_T);
      function P1 (X : Integer) return Integer renames Wrap_Test_P1_087c71_fe3908;
   begin
      AUnit.Assertions.Assert
        (P1 (3) = 4,
         "Test failed.");
   end Test_P1_087c71_fe3908;

--  GNATtest marker section
--  PLEASE DO NOT MODIFY OR REMOVE THIS SECTION
--  test routine end
--  end of GNATtest marker section

   function Wrap_Test_P2_7727fe_cdf8e0 (X : Integer)  return Integer
   is
   begin
      AUnit.Assertions.Assert
        (X < 16,
         "req_sloc(pack.ads:23):test case 2 precondition violated");
      declare
         Test_P2_7727fe_cdf8e0_Result : constant Integer := GNATtest_Generated.GNATtest_Standard.Pack.P2 (X);
      begin
         AUnit.Assertions.Assert
           (Test_P2_7727fe_cdf8e0_Result < 4,
            "ens_sloc(pack.ads:24:):test case 2 postcondition violated");
         return Test_P2_7727fe_cdf8e0_Result;
      end;
   end Wrap_Test_P2_7727fe_cdf8e0;
--  GNATtest marker section
--  PLEASE DO NOT MODIFY OR REMOVE THIS SECTION
--  test routine beginning
--  hash: 7727fe42ea1acec80a3f5aa8a67b467ff4aa4e41
--  test case hash: cdf8e0c1eb7807ced9de2208096e373bceda32b9
--  hash version: 1
--  end of GNATtest marker section

   procedure Test_P2_7727fe_cdf8e0 (Gnattest_T : in out Test) is
      pragma Unreferenced (Gnattest_T);
      function P2 (X : Integer) return Integer renames Wrap_Test_P2_7727fe_cdf8e0;
   begin
      AUnit.Assertions.Assert
        (P2 (1) = 3,
         "Test failed.");
   end Test_P2_7727fe_cdf8e0;

--  GNATtest marker section
--  PLEASE DO NOT MODIFY OR REMOVE THIS SECTION
--  test routine end
--  end of GNATtest marker section

   function Wrap_Test_P3_72ef10_519ea0 (X : Integer)  return Integer
   is
   begin
      AUnit.Assertions.Assert
        (((X <= Integer'Last - 1)) and (X < 16),
         "req_sloc(pack.ads:33):test case 3 precondition violated");
      declare
         Test_P3_72ef10_519ea0_Result : constant Integer := GNATtest_Generated.GNATtest_Standard.Pack.P3 (X);
      begin
         AUnit.Assertions.Assert
           (((Test_P3_72ef10_519ea0_Result = X + 5)) and (Test_P3_72ef10_519ea0_Result < 4),
            "ens_sloc(pack.ads:34:):test case 3 postcondition violated");
         return Test_P3_72ef10_519ea0_Result;
      end;
   end Wrap_Test_P3_72ef10_519ea0;
--  GNATtest marker section
--  PLEASE DO NOT MODIFY OR REMOVE THIS SECTION
--  test routine beginning
--  hash: 72ef104234340afe883f05e874a44f03b7e4235f
--  test case hash: 519ea0fe9660c32cc488b72a6f3b172ebdbb6fc4
--  hash version: 1
--  end of GNATtest marker section

   procedure Test_P3_72ef10_519ea0 (Gnattest_T : in out Test) is
      pragma Unreferenced (Gnattest_T);
      function P3 (X : Integer) return Integer renames Wrap_Test_P3_72ef10_519ea0;
   begin
      AUnit.Assertions.Assert
        (Gnattest_Generated.Default_Assert_Value,
         "Test not implemented.");
   end Test_P3_72ef10_519ea0;

--  GNATtest marker section
--  PLEASE DO NOT MODIFY OR REMOVE THIS SECTION
--  test routine end
--  end of GNATtest marker section

   function Wrap_Test_P4_0599a5_76a6c4 (X : Integer)  return Integer
   is
   begin
      AUnit.Assertions.Assert
        (X < 16,
         "req_sloc(pack.ads:43):test case 4 precondition violated");
      declare
         Test_P4_0599a5_76a6c4_Result : constant Integer := GNATtest_Generated.GNATtest_Standard.Pack.P4 (X);
      begin
         AUnit.Assertions.Assert
           (Test_P4_0599a5_76a6c4_Result <= 4,
            "ens_sloc(pack.ads:44:):test case 4 postcondition violated");
         return Test_P4_0599a5_76a6c4_Result;
      end;
   end Wrap_Test_P4_0599a5_76a6c4;
--  GNATtest marker section
--  PLEASE DO NOT MODIFY OR REMOVE THIS SECTION
--  test routine beginning
--  hash: 0599a57e83526849ce07f90c0d3e524e77b8ccbf
--  test case hash: 76a6c46c0cbd5bd6063e94c57f17d99bfbae1b69
--  hash version: 1
--  end of GNATtest marker section

   procedure Test_P4_0599a5_76a6c4 (Gnattest_T : in out Test) is
      pragma Unreferenced (Gnattest_T);
      function P4 (X : Integer) return Integer renames Wrap_Test_P4_0599a5_76a6c4;
   begin
      AUnit.Assertions.Assert
        (P4 (0) = 4,
         "Test failed.");
   end Test_P4_0599a5_76a6c4;

--  GNATtest marker section
--  PLEASE DO NOT MODIFY OR REMOVE THIS SECTION
--  test routine end
--  end of GNATtest marker section

--  GNATtest marker section
--  PLEASE DO NOT MODIFY OR REMOVE THIS SECTION
--  test routine beginning
--  hash: c008022c109aa3cdc42dc9097e062c1550e5cc01
--  hash version: 1
--  end of GNATtest marker section

   procedure Test_P5_c00802 (Gnattest_T : in out Test) is
      pragma Unreferenced (Gnattest_T);
   begin
      AUnit.Assertions.Assert
        (Gnattest_Generated.Default_Assert_Value,
         "Test not implemented.");
   end Test_P5_c00802;

--  GNATtest marker section
--  PLEASE DO NOT MODIFY OR REMOVE THIS SECTION
--  test routine end
--  end of GNATtest marker section

--  GNATtest marker section
--  PLEASE DO NOT MODIFY OR REMOVE THIS SECTION
--  test routine beginning
--  hash: 0371dfc4a0cecf0f11e47de79a3ece5a63ec6825
--  hash version: 1
--  end of GNATtest marker section

   procedure Test_P6_0371df (Gnattest_T : in out Test) is
      pragma Unreferenced (Gnattest_T);
   begin
      AUnit.Assertions.Assert
        (Gnattest_Generated.Default_Assert_Value,
         "Test not implemented.");
   end Test_P6_0371df;

--  GNATtest marker section
--  PLEASE DO NOT MODIFY OR REMOVE THIS SECTION
--  test routine end
--  end of GNATtest marker section

end Pack.Test_Data.Tests;

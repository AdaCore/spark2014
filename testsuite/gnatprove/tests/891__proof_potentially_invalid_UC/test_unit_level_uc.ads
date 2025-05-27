pragma SPARK_Mode;

with Ext; use Ext;
with Ada.Unchecked_Conversion;
function Test_Unit_Level_UC is new Ada.Unchecked_Conversion (Integer, R) with Potentially_Invalid;

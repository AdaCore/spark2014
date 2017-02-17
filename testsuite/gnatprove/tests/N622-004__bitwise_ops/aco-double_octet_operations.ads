---------------------------------------------------------------------------
-- FILE    : aco-double_octet_operations.ads
-- SUBJECT : Intrinsic and related operations for ACO.Double_Octet
-- AUTHOR  : (C) Copyright 2014 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

--# inherit ACO;
package ACO.Double_Octet_Operations is

   function Shift_Left(Value : ACO.Double_Octet; Count : Natural) return ACO.Double_Octet
     with
       Import,
       Convention => Intrinsic,
       Global     => null;

   function Shift_Right(Value : ACO.Double_Octet; Count : Natural) return ACO.Double_Octet
     with
       Import,
       Convention => Intrinsic,
       Global     => null,
       Post       => Shift_Right'Result = Value / (2**Count);

   function Rotate_Left(Value : ACO.Double_Octet; Count : Natural) return ACO.Double_Octet
     with
       Import,
       Convention => Intrinsic,
       Global     => null;

   function Rotate_Right(Value : ACO.Double_Octet; Count : Natural) return ACO.Double_Octet
     with
       Import,
       Convention => Intrinsic,
       Global     => null;

   procedure Xor_Array
     (Accumulator  : in out ACO.Double_Octet_Array;
      Incoming     : in     ACO.Double_Octet_Array;
      Success_Flag : out    Boolean)
     with
       Depends => ((Accumulator, Success_Flag) => (Accumulator, Incoming));

end ACO.Double_Octet_Operations;

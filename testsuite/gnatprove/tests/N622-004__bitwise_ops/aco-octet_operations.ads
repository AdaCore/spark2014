---------------------------------------------------------------------------
-- FILE    : aco-octet_operations.ads
-- SUBJECT : Intrinsic and related operations for ACO.Octet
-- AUTHOR  : (C) Copyright 2014 by Peter C. Chapin
--
-- Please send comments or bug reports to
--
--      Peter C. Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package ACO.Octet_Operations is

   function Shift_Left(Value : ACO.Octet; Count : Natural) return ACO.Octet
     with
       Import,
       Convention => Intrinsic,
       Global     => null;

   function Shift_Right(Value : ACO.Octet; Count : Natural) return ACO.Octet
     with
       Import,
       Convention => Intrinsic,
       Global     => null,
       Post       => Shift_Right'Result = Value / (2**Count);

   function Rotate_Left(Value : ACO.Octet; Count : Natural) return ACO.Octet
     with
       Import,
       Convention => Intrinsic,
       Global     => null;

   function Rotate_Right(Value : ACO.Octet; Count : Natural) return ACO.Octet
     with
       Import,
       Convention => Intrinsic,
       Global     => null;

   procedure Xor_Array
     (Accumulator  : in out ACO.Octet_Array;
      Incoming     : in     ACO.Octet_Array;
      Success_Flag : out    Boolean)
     with
       Depends => ((Accumulator, Success_Flag) => (Accumulator, Incoming));

end ACO.Octet_Operations;

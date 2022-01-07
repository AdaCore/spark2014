with Interfaces;
use Interfaces;

package X86
  with SPARK_Mode
is
   subtype Unsigned8  is Interfaces.Unsigned_8;

   -----------------------------------------------------------------------
   --		   Definition of AL, AH, AX, EAX, and RAX		--
   -----------------------------------------------------------------------

   AL_TEST : Unsigned8 := 0;

   function AL return Unsigned8 with
     Global => (Input => AL_TEST),
     Post => (AL'Result = Unsigned8(AL_TEST and 16#FF#));

   procedure Write_AL(Val : in Unsigned8) with
     Global => (In_Out => AL_TEST),
     Post => ((AL = Val) and ((AL_TEST and 16#00#) = (AL_TEST'Old and 16#00#)));


end X86;

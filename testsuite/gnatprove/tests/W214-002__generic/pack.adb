with Gen;
package body Pack is

   procedure P is
      procedure Should_Prove is new Gen.Incr (Integer);
      procedure Should_Skip is new Gen.Incr_Annot (Integer);
   begin
      null;
   end P;

   procedure Annot is
      procedure Should_Skip1 is new Gen.Incr (Integer);
      procedure Should_Skip2 is new Gen.Incr_Annot (Integer);
   begin
      null;
   end Annot;

end Pack;

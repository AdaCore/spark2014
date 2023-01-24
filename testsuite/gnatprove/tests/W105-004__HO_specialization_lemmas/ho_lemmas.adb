procedure HO_Lemmas
  with
    SPARK_Mode => On
is

   function Rand (X : Integer) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);

   --  Function with higher order specialization

   function Call (F : not null access function return Integer) return Integer is
     (F.all)
     with Annotate => (GNATprove, Higher_Order_Specialization);

   --  Lemma procedure giving its definition

   procedure Call_Def (F : not null access function return Integer) with
     Ghost,
     Annotate => (GNATprove, Higher_Order_Specialization),
     Post => Call (F) = F.all;

   procedure Call_Def (F : not null access function return Integer) is null;

   V : Integer := 0;
   function Read_V return Integer is (V);

   I : Integer;

begin
   if Rand (1) then
      I := Call (Read_V'Access);

      --  The definition should not be available on specializations as bodies
      --  of expression functions are never specialized.

      pragma Assert (I = 0); --@ASSERT:FAIL
   else
      --  The direct call to Call and the call in the postcondition of Call_Def
      --  should use the same specialization so the assertion should be
      --  provable.
      --
      I := Call (Read_V'Access);
      Call_Def (Read_V'Access);
      pragma Assert (I = 0); --@ASSERT:PASS
   end if;
end HO_Lemmas;

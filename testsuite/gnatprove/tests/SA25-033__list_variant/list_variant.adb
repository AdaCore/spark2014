procedure List_Variant with SPARK_Mode is

   type List;
   type List_Acc is access List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   function Length_Ann (L : access constant List; Max : Natural := Natural'Last) return Natural with
     Subprogram_Variant => (Decreases => Max),
     Annotate => (GNATprove, Terminating),
     Post => Length_Ann'Result <= Max;

   function Length_Ann (L : access constant List; Max : Natural := Natural'Last) return Natural is
     (if L = null then 0 elsif Max = 0 then 0 else Length_Ann (L.N, Max - 1) + 1);

   procedure Prove_Length_Max (L : access constant List; Max1, Max2 : Natural) with
     Global => null,
     Pre    => Max1 > Max2,
     Subprogram_Variant => (Decreases => Max1),
     Post   => Length_Ann (L, Max2) = Natural'Min (Length_Ann (L, Max1), Max2)
   is
   begin
      if L /= null and Max2 /= 0 then
         Prove_Length_Max (L.N, Max1 - 1, Max2 - 1);
      end if;
   end Prove_Length_Max;

   procedure Prove_Length_Def (L : access constant List) with
     Global => null,
     Post   => Length_Ann (L) =
       (if L = null then 0
        elsif Length_Ann (L.N) = Natural'Last then Natural'Last
        else Length_Ann (L.N) + 1)
   is
   begin
      if L /= null then
         Prove_Length_Max (L.N, Natural'Last, Natural'Last - 1);
      end if;
   end Prove_Length_Def;
begin
   null;
end;

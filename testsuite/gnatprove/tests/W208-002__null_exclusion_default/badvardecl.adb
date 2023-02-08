procedure Badvardecl with SPARK_Mode => On is
   type Int_Access is access constant Integer;

   type Field is (A, B);

   type Discr_Rec (Kind : Field := A) is
      record
         case Kind is
            when A =>
               F : not null Int_Access;--@NULL_EXCLUSION:FAIL
            when B =>
               null;
         end case;
      end record;

   Result : Discr_Rec;
begin
   null;
end Badvardecl;

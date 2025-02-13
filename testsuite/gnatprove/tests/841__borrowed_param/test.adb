procedure Test with SPARK_Mode is

   type Holder is record
      C : aliased Integer;
   end record;

   function F_1 (X : access Holder) return not null access Integer;

   function F_1 (X : access Holder) return not null access Integer is
      B : not null access Integer := X.C'Access;
   begin
      B.all := 15;
      return B;
   end F_1;

   function F_2 (X : access Holder) return not null access Integer;

   function F_2 (X : access Holder) return not null access Integer is

      procedure Update (X : access Integer) with
        Always_Terminates,
        Global => null,
        Import;

      B : not null access Integer := X.C'Access;
   begin
      Update (B);
      return B;
   end F_2;

   function F_3 (X : access Holder) return not null access Integer;

   function F_3 (X : access Holder) return not null access Integer is
      B : not null access Integer := X.C'Access;
   begin
      declare
         B2 : not null access Integer := B;
      begin
         B2.all := 15;
      end;
      return B;
   end F_3;
begin
   null;
end;

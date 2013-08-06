procedure Xor_Mod is
   type T is mod 256;

   function My_Xor (A, B : T) return T is
   begin
      return A xor B;
   end My_Xor;

   function Xor_1 (A : T) return T is
   begin
      return A xor 2;
   end;

   function And_1 (A, B : T) return T is
   begin
      return A and B;
   end And_1;

   function And_2 (A : T) return T is
   begin
      return A and 2;
   end And_2;

   function Or_1 (A, B : T) return T is
   begin
      return A or B;
   end;

   function Or_2 (A : T) return T is
   begin
      return A or 2;
   end;

   Z : T;
begin
   Z := My_Xor (1, 2);
   Z := Xor_1 (1);
   Z := And_1 (1, 2);
   Z := And_2 (1);
   Z := Or_1 (1, 2);
   Z := Or_2 (1);
end Xor_Mod;

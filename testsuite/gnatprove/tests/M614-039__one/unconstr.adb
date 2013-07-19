package body Unconstr is

   procedure P is
   begin
      null;
   end;

   function Equality (S1, S2 : String) return Boolean
      with Post => (Equality'Result = (S1 = S2));

   function Equality (S1, S2 : String) return Boolean
   is
   begin
      return S1 = S2;
   end Equality;

   function Constr_Call return Boolean
      with Post => Constr_Call'Result = True;

   function Constr_Call return Boolean is
      B : Boolean;
      S : String (1 .. 10) := (others => ' ');
      S2 : String (12 .. 21) := (others => ' ');
   begin
      B := Equality (S, S2);
      return B;
   end Constr_Call;

   function Unconstr_Call (S1, S2 : String) return Boolean
      with Post => Unconstr_Call'Result = (S1 = S2);

   function Unconstr_Call (S1, S2 : String) return Boolean
   is
   begin
      return Equality (S1, S2);
   end Unconstr_Call;

   subtype S is String (1 .. 10);

   function Constr_Return (X : Integer) return S
   is
      pragma Unreferenced (X);
   begin
      return (others => ' ');
   end Constr_Return;

   procedure Constr_Return_Call (X : Integer)
   is
      S : String := Constr_Return (X);
   begin
      for I in S'Range loop
         S (I) := ' ';
      end loop;
   end Constr_Return_Call;

   function Unconstr_Return (X : Integer) return String
      with Post => Unconstr_Return'Result'First = 1 and Unconstr_Return'Result'Last = X;

   function Unconstr_Return (X : Integer) return String
   is
      S : String (1 .. X) := (others => ' ');
   begin
      return S;
   end Unconstr_Return;

end Unconstr;

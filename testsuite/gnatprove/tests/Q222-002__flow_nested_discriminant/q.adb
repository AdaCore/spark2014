procedure Q with Global => null is

   type T (D : Integer) is null record;

   type TT (D : Integer) is record
      Component : T (D => D);
   end record;

   procedure P (X : in out T) with Pre => True is


      type T2 is record
         C1 : Integer := X.D;  --  NOK
      end record;
   begin
      null;
   end P;

   procedure Q (X : in out TT) with Pre => True is


      type T2 is record
         C1 : Integer := X.Component.D;  --  NOK
      end record;
   begin
      null;
   end Q;
begin
   null;
end Q;

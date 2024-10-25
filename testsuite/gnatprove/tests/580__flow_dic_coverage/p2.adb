procedure P2 is
   package P is
      type T is tagged private with Default_Initial_Condition;
   private
      type T is tagged record
         C : Natural := 0;
      end record;
   end P;

   type TT is new P.T with record
      X : Natural;
      Y : Natural := 123;
   end record;
begin
   null;
end;

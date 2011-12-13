procedure pack is

   generic
      type T is digits <>;
      F : T;
   procedure P;

   procedure P is
   begin
      null;
   end P;

   procedure P1 is
      new P (Float, Float'First);

begin
   null;
end pack;

package body Lili is
   pragma SPARK_Mode (Off);
   type Integer_Access is access Integer;

   type Iterator is
   record
      Container : Integer_Access;
   end record;

   procedure Finalize (Object : in out Iterator);

   function Next (Position : Cursor) return Cursor is
   begin
      return Position;
   end Next;

   procedure Finalize (Object : in out Iterator) is
      X : Integer := Object.Container.all;
      K : Cursor := Cursor'(Container => 1);
      Y : Cursor := Next (K);
   begin
      null;
   end Finalize;

end Lili;

procedure Main with SPARK_Mode is
   type Rec is record
      X : Integer;
      Y : Integer;
   end record;

   Y : Rec := (others => 1);

   type Holder is record
      F : Integer;
      G : Rec;
   end record;

   H : Holder := (F => 1, G => Y);

   procedure Test with Global => (Input => H) is
      E : Holder := (declare
                       Z : constant Rec := H.G;
                     begin (H with delta G => (Z with delta Y => 1)));
   begin
      null;
   end Test;

begin
   null;
end Main;

procedure Toy1 with Spark_Mode is
   subtype Data_Size is Natural range 0 .. 256;
   type Data (Size : Natural := 0) is record
      Str : String (1 .. Size);
   end record;
   type Message is record
      Number : Natural;
      Payload : Data;
   end record;

   M : Message;
   P : Data (20) with Relaxed_Initialization;
begin
   for I in 1 .. 20 loop
      P.Str (I) := Character'Val (64 + I);
   end loop;

   M := (Number => 3,
         Payload => P);
end Toy1;

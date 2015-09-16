package body Test
with
   SPARK_Mode => On
is

   procedure May_Fail (I : Integer; Success : out Boolean) is
   begin
      Success := I > 10;
   end May_Fail;

   function Test_Smthng (I : Integer) return Boolean is
   begin
      return I < 5;
   end Test_Smthng;

   procedure Test2
     (I        : in     Integer;
      Done     :    out Boolean;
      Success  :    out Boolean)
   is
   begin
      May_Fail (I, Success);

      if Success then
         Done := Test_Smthng (I);
      end if;
   end Test2;

   procedure Test1 (I : Integer; Success : out Boolean)
   is
      Done : Boolean := False;
   begin
      Test2 (I, Done, Success);
      Success := Success and Done;
   end Test1;

end Test;

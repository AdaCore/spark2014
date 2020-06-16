with Streamable_Types; use Streamable_Types;
with Ada.Text_IO.Text_Streams;
use  Ada.Text_IO;

procedure Main with SPARK_Mode is
begin
   Int'Write (Text_Streams.Stream (Current_Output), 42);
end Main;

with Types; use Types;
procedure Use_Types with
  SPARK_Mode
is
   X : T (3) with Unreferenced;
begin
   null;
end Use_Types;

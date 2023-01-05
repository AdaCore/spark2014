with Types; use Types;

procedure Use_Types with SPARK_Mode is
   V : T (False); --  V.Y is not initialized
begin
   Write_Part (V, False);  --  Write_Part does not initialize V.Y
   if V.Y = 0 then  --  Read an unitialized variable...
      null;
   end if;
end Use_Types;

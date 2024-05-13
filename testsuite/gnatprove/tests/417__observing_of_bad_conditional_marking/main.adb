
procedure Main with SPARK_Mode is
   type A is access Integer;
   X : A := new Integer'(0);
   Y : access Integer := X;
   Z : A := new Integer'(1);
   T : access constant Integer := (if Y.all = 0 then Y else Z);
   --  Bad observer: distinct root objects.

   U : access constant Integer :=
       (case Y.all is
          when 0 => Y,
          when 1 => Y,
          when others => Z);
   -- Bad observer: distinct root objects.

   function F (X : access Integer) return access Integer is (X);

   V : access constant Integer := F(if Y.all = 0 then Y else Y);
   --  Unsupported observer: if-expression is not top-level.

   W : access constant Integer :=
       F(case Y.all is
          when 0 => Y,
          when 1 => Y,
          when 2 => Y,
          when others => Y);
   --  Unsupported observer: case-expression is not top-level.
begin
   null;
end Main;

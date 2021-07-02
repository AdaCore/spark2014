package P with SPARK_Mode is
   type T is access Boolean;
   X : constant T := null;
   function F return Boolean with Global => X;
end;

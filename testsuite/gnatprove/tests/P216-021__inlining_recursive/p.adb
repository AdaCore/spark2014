procedure P
with SPARK_Mode => On
is

 type T is range 25 ..26;

 procedure P (V:T) is
 begin
   case V is
     when T'First .. 24 => P(V-1);
     when 25 .. T'Last  => P(V-1);
   end case;
 end;

 X : constant T := 25;
begin
 P(X);
end;

package Bar
with
   SPARK_Mode => On
is

   ID : constant Natural
   with
      Import,
      Convention => C,
      Link_Name  => "cpu_id";

end Bar;

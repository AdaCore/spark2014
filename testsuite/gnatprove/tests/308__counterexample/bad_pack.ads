package Bad_Pack with
   SPARK_Mode => On
is
   procedure Foo (X : in out Boolean; Y : in Boolean) with
      Post => Y;
end Bad_Pack;

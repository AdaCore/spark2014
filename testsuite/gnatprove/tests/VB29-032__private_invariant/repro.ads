package Repro with
   SPARK_Mode => On
is
   type Calendar_T is private;
private

   package Lists is
      type List is private;
   private
      type Controlled is tagged null record;
      type List is new Controlled with null record;
   end Lists;

   type Calendar_T is new Lists.List
     with Type_Invariant => True;

end Repro;

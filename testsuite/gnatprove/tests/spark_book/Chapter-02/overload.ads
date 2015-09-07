package Overload is

   procedure Calc (A : in  Integer;
                   C : out Integer);

   procedure Calc (A : in  Integer;
                   C : out Float);


   procedure Calc (A : in  Integer;
                   B : in  Integer;
                   C : out Integer);
end Overload;

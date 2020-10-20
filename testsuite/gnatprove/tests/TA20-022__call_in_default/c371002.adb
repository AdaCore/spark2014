procedure C371002 is

   subtype Small_Int is Integer range 1..10;
   type My_Array is array (Small_Int range <>) of Integer;
   function Func1 return Integer is (1);

   type Rec_Of_MyArr_01 (D3 : Integer) is
      record
         C1 : My_Array (Func1 .. D3);
      end record;

   type Rec_Of_Rec_Of_MyArr is
      record
         C1 : Rec_Of_MyArr_01(1);
      end record;

   Obj6 : Rec_Of_Rec_Of_MyArr;
begin
   if Obj6 /= (C1 => (1, (1 => 1))) then
      null;
   end if;
end C371002;

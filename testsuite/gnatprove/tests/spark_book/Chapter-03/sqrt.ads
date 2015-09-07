   function Sqrt (Item : in Natural) return Natural
      with
         Post => Sqrt'Result ** 2 <= Item and then
                 (Sqrt'Result + 1) ** 2 > Item;

package P is
   protected type Outer_Type is
      function Outer_Fun return Integer;
   private
      Outer_Data : Integer := 0;
   end;
end;

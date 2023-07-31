package blip is


function Square (X : in Integer) return Integer
  with SPARK_Mode,
  Global => null,
  Pre => X < Integer'Last,
  Post => Square'Result < Integer'Last,
  Depends => (Square'Result => X);

end blip;

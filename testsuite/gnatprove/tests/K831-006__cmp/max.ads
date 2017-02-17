package Max is

   function Max (Left, Right : Float) return Float
     with Post => (if Right > Left then
                     Max'Result = Right
                  else
                     Max'Result = Left);

end Max;

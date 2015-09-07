package Searches
with Spark_Mode
is

   type Array_Type is array (Positive range <>) of Integer;

   procedure Find_First (List     : in  Array_Type;
                         Value    : in  Integer;
                         Position : out Positive)
      with
         Depends => (Position => (List, Value)),
         Pre     => (for some Index in List'Range => List (Index) = Value),
         Post    => (Position in List'Range and then
                     List (Position) = Value and then
                     (for all Index in List'First .. Position - 1 =>
                         List (Index) /= Value));

   procedure Find_Only  (List     : in Array_Type;
                         Value    : in Integer;
                         Found    : out Boolean;
                         Position : out Positive)
      with
         Depends => ((Found, Position) => (List, Value)),
         Pre     => (List'Length > 0 and then
                     List'Last < Positive'Last and then
                     (for all J in List'Range =>
                        (for all K in List'Range =>
                           (if List (J) = List (K) then J = K)))),
         Post    => (Position in List'Range and then
                     ((Found and then List (Position) = Value)
                             or else
                      (not Found and then Position = List'Last and then
                      (for all J in List'Range => List (J) /= Value))));
   end Searches;

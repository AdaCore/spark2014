package Q_14
  with SPARK_Mode,
       Abstract_State => Q_State,
       Initializes    => Q_State
is
   type T is new Integer;

   procedure Init (S : out T);
end Q_14;

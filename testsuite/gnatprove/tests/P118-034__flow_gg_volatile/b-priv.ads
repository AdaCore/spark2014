private package B.Priv with
   Abstract_State => ((State with Part_Of => B.State),
                      (Atomic_State with External, Part_Of => B.Atomic_State))
is

   procedure P_Read_State (X : out Boolean);
   procedure P_Read_Atomic_State (X : out Boolean);

end B.Priv;

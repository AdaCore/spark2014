with Lib.Cont.G_B;


generic package Lib.MLM.G_FUM_Cm.G_Q is

   package Q is
      new Cont.G_B (T_E => T_FUM_Cm);

   type T_Q is
      new Q.T with private;

private

   type T_Q is
      new Q.T with null record;

end Lib.MLM.G_FUM_Cm.G_Q;

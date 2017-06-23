package Rec_Post is
   function Is_Even (I : Natural) return Boolean with
     Post => Is_Even'Result = (I = 0 or else Is_Odd (I - 1));
   pragma Annotate (GNATprove, Terminating, Is_Even);

   function Is_Odd (I : Natural) return Boolean with
     Post => Is_Odd'Result = (I /= 0 and then Is_Even (I - 1));
   pragma Annotate (GNATprove, Terminating, Is_Odd);
end;

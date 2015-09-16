package Synchronous_Barriers is

   subtype Barrier_Limit is Positive range 1 .. Positive'Last;

   type Synchronous_Barrier (Release_Threshold : Barrier_Limit) is
      limited private;

private
   protected type Synchronous_Barrier (Release_Threshold : Barrier_Limit) is
   end Synchronous_Barrier;

end Synchronous_Barriers;

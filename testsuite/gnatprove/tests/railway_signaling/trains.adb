package body Trains with
  SPARK_Mode
is

   procedure Update_Track_Signal (Track : Track_Id) with
     Global => (Input  => (Trains, Cur_Num_Trains),
                In_Out => Track_Signals),
     Pre  => Track_Signals (Track) = Orange,
     Post => (if (for some T in Train_Id range 1 .. Cur_Num_Trains =>
                    Is_Previous_Track (Trains (T), Track))
              then
                 Track_Signals (Track) = Orange
              else
                 Track_Signals (Track) = Green)
                and then
             (for all Other_Track in Track_Id =>
                (if Other_Track /= Track then
                   Track_Signals (Other_Track) = Track_Signals'Old (Other_Track)));
   --  Possibly update a signal for a track from Orange to Green if it's ok to
   --  do so.

   -------------------------
   -- Update_Track_Signal --
   -------------------------

   procedure Update_Track_Signal (Track : Track_Id) is
   begin
      for Train in Train_Id range 1 .. Cur_Num_Trains loop
         if Is_Previous_Track (Trains (Train), Track) then
            return;
         end if;

         pragma Loop_Invariant
           (for all T in 1 .. Train =>
               not Is_Previous_Track (Trains (T), Track));
      end loop;

      Track_Signals (Track) := Green;
   end Update_Track_Signal;

   ----------
   -- Move --
   ----------

   procedure Move
     (Train        : Train_Id;
      New_Position : Train_Position;
      Result       : out Move_Result)
   is
      Cur_Position : constant Train_Position := Trains (Train);
      Prev : Track_Opt_Id;
   begin
      if Moving_Inside_Current_Tracks (Cur_Position, New_Position) then
         Result := Keep_Going;
         Trains (Train) := New_Position;

         pragma Assert (Occupied_Tracks_On_Red);
         pragma Assert
           (for all Train in Train_Id range 1 .. Cur_Num_Trains =>
              (for all Id in Prev_Id =>
                   (if Get_Previous_Track (Trains (Train), Id) /= No_Track_Id then
                         Track_Signals (Get_Previous_Track (Trains (Train), Id)) in
                      Orange | Red)));
         pragma Assert
           (for all Train in Train_Id range 1 .. Cur_Num_Trains =>
              (for all Id in Prev_Id =>
                   (if Get_Other_Previous_Track (Trains (Train), Id) /= No_Track_Id then
                         Track_Signals (Get_Other_Previous_Track (Trains (Train), Id)) in
                      Orange | Red)));
         pragma Assert (Previous_Tracks_On_Orange_Or_Red);
         pragma Assert (Safe_Signaling);

      elsif Moving_Away_From_Current_Track (Cur_Position, New_Position) then
         Result := Keep_Going;
         Trains (Train) := New_Position;

         pragma Assert (Previous_Tracks_On_Orange_Or_Red);

         --  the track leaved goes from Red to Orange

         Track_Signals (Cur_Position.Track_End) := Orange;

         pragma Assume (No_Track_Precedes_Itself);
         pragma Assert (Occupied_Tracks_On_Red);
         pragma Assert (Previous_Tracks_On_Orange_Or_Red);

         --  the signal for tracks that precede the track leaved must be
         --  updated, depending on the position of other trains. No update is
         --  needed if the signal on such a track is Red, as this means some
         --  train is on the track. So only update the signal if it is Orange.

         for Id in Prev_Id loop
            Prev := Get_Previous_Track (Cur_Position, Id);

            if Prev /= No_Track_Id
              and then Track_Signals (Prev) = Orange
            then
               Update_Track_Signal (Prev);
            end if;

            pragma Loop_Invariant
              (for all J in Track_Id =>
                 ((if Track_Signals'Loop_Entry (J) = Red then Track_Signals (J) = Red)
                     and then
                  (if Track_Signals'Loop_Entry (J) = Orange and then
                     (for some T in Train_Id range 1 .. Cur_Num_Trains =>
                        Is_Previous_Track (Trains (T), J))
                   then Track_Signals (J) = Orange)));
         end loop;

         pragma Assume (No_Track_Precedes_Itself);
         pragma Assert (Occupied_Tracks_On_Red);
         pragma Assert (Previous_Tracks_On_Orange_Or_Red);
         pragma Assert (Safe_Signaling);

      --   otherwise, the train is moving in a new track

      else

         case Track_Signals (New_Position.Track_Begin) is
            when Red =>
               Result := Stop;

            when others =>
               if Track_Signals (New_Position.Track_Begin) = Green then
                  Result := Full_Speed;
               else
                  Result := Slow_Down;
               end if;

               pragma Assert
                 (for all Id in Prev_Id =>
                    (if Get_Previous_Track (New_Position, Id) /= No_Track_Id then
                          Track_Signals (Get_Previous_Track (Trains (Train), Id)) in
                         Orange | Red));

               Trains (Train) := New_Position;
               Track_Signals (New_Position.Track_Begin) := Red;

               for Id in Prev_Id loop
                  Prev := Get_Other_Previous_Track (New_Position, Id);

                  if Prev /= No_Track_Id
                    and then Track_Signals (Prev) = Green
                  then
                     Track_Signals (Prev) := Orange;
                  end if;

                  pragma Loop_Invariant
                    (for all K in Track_Ids'First .. Id =>
                       (if Get_Other_Previous_Track (New_Position, K) /= No_Track_Id then
                          Track_Signals (Get_Other_Previous_Track (New_Position, K)) in
                            Orange | Red));
                  pragma Loop_Invariant
                    (for all J in Track_Id =>
                       ((if Track_Signals'Loop_Entry (J) = Red then Track_Signals (J) = Red)
                           and then
                        (if Track_Signals'Loop_Entry (J) = Orange then Track_Signals (J) = Orange)));
                  pragma Loop_Invariant
                    (for all Train in Train_Id range 1 .. Cur_Num_Trains =>
                       (for all Id in Prev_Id =>
                            (if Get_Previous_Track (Trains (Train), Id) /= No_Track_Id then
                                  Track_Signals (Get_Previous_Track (Trains (Train), Id)) in
                               Orange | Red)));
               end loop;

               pragma Assert (Occupied_Tracks_On_Red);
               pragma Assert (Previous_Tracks_On_Orange_Or_Red);
               pragma Assert (Safe_Signaling);
         end case;
      end if;
   end Move;

end Trains;

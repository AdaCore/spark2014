package body Pupils with SPARK_Mode
is

 procedure AddPupil (SName, FName: in PupilName; Fm: in FormType;
                      Subj0: in Subject; Score0: in Percentage;
                      Subj1: in Subject; Score1: in Percentage;
                      Subj2: in Subject; Score2: in Percentage;
                      Subj3: in Subject; Score3: in Percentage;
                      Subj4: in Subject; Score4: in Percentage;
                      Subj5: in Subject; Score5: in Percentage;
                      Subj6: in Subject; Score6: in Percentage;
                      Subj7: in Subject; Score7: in Percentage;
                      Subj8: in Subject; Score8: in Percentage;
                      Subj9: in Subject; Score9: in Percentage;
                      P: in out PupilData; Success: out Boolean)
  is
     Subject_Scores : Subject_Score_Pair_List;
  begin
     Subject_Scores :=
       ((Subj0, Score0), (Subj1, Score1), (Subj2, Score2), (Subj3, Score3),
        (Subj4, Score4), (Subj5, Score5), (Subj6, Score6), (Subj7, Score7),
        (Subj8, Score8), (Subj9, Score9));
     for I in Subject_Scores'Range loop
        Success :=
          not P.PupilEntries ((P.NumberOfPupils + 1)).Scores
             (Subject_Scores (I).Subj).Studying;
        exit when not Success;
        -- It is not a duplicate - mark as studying and add the score
        P.PupilEntries ((P.NumberOfPupils + 1)).Scores
          (Subject_Scores (I).Subj).Score := Subject_Scores (I).Score;
     end loop;
     if Success then
        P.NumberOfPupils := P.NumberOfPupils + 1;
        P.PupilEntries (P.NumberOfPupils).Surname := SName;
        P.PupilEntries (P.NumberOfPupils).Forename := FName;
        P.PupilEntries (P.NumberOfPupils).Form := Fm;
     end if;

  end AddPupil;

end Pupils;


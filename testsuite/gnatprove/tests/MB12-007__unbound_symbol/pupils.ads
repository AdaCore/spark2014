package Pupils with SPARK_Mode is
  pragma Unevaluated_Use_Of_Old(Allow);
  MaxPupils: constant Natural := 250;

  subtype Percentage is Natural range 0..100;

  type Participation is record
    Studying: Boolean;
    Score:    Percentage;
  end record;

  Null_Participation: constant Participation :=
    Participation'(Studying => False, Score => Percentage'First);

  type Subject is (EnglishLanguage,
                   EnglishLiterature,
                   Mathematics,
                   French,
                   German,
                   Spanish,
                   Biology,
                   Chemistry,
                   Physics,
                   GeneralScience,
                   History,
                   Geography,
                   Economics,
                   Computing,
                   Art,
                   Music,
                   HomeEconomics,
                   DesignAndTechnology,
                   NoSubject
		     -- used for pupils taking less than 10 subjects
                  );

  type ResultsType is array (Subject) of Participation;

  Null_Results: constant ResultsType :=
    ResultsType'(others => Null_Participation);

  subtype NameIndex is Natural range 1..25;

  subtype PupilName is String(NameIndex);

  Null_Name: constant PupilName := PupilName'(others => ' ');

  type FormType is (B1, B2, C1, C2, N1, N2, S1, S2, NoForm);

  type PupilType is record
    Surname, Forename: PupilName;
    Form: FormType;
    Scores: ResultsType;
  end record;

  Null_Pupil: constant PupilType :=
    PupilType'(Surname  => Null_Name,
               Forename => Null_Name,
               Form     => NoForm,
               Scores   => Null_Results);

  subtype PupilNumbers is Natural      range 0..MaxPupils;
  subtype PupilIndex   is PupilNumbers range 1..MaxPupils;

  type PupilArray is array (PupilIndex) of PupilType;

  type PupilData is record
    NumberOfPupils: PupilNumbers;
    PupilEntries:   PupilArray;
    -- Invariant: only 1..PupilNumbers of the PupilEntries
    -- array have been populated
  end record;

  Null_PupilData: constant PupilData :=
    PupilData'(NumberOfPupils => 0,
    PupilEntries => PupilArray'(others => Null_Pupil));


  type Subject_List is array (0 .. 9) of Subject;

  type Subject_Score_Pair is record
     Subj  : Subject;
     Score : Percentage;
  end record;

  type Subject_Score_Pair_List is array (0 .. 9) of Subject_Score_Pair;

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
    with
       Pre  => P.NumberOfPupils < MaxPupils and Fm /= NoForm,
       Post => (for all I in PupilNumbers range 1 .. P'Old.NumberOfPupils =>
                  P.PupilEntries (I) = P'Old.PupilEntries (I)) and
               (if Success then
                  (for all I in 0 .. 9 => (for all J in 0 .. 9 =>
                      (if I /= J then
                        (Subject_List'(Subj0, Subj1, Subj2, Subj3, Subj4,
                                       Subj5, Subj6, Subj7, Subj8, Subj9) (I) /=
                         Subject_List'(Subj0, Subj1, Subj2, Subj3, Subj4,
                                       Subj5, Subj6, Subj7, Subj8, Subj9) (J))
                      or
                        (Subject_List'(Subj0, Subj1, Subj2, Subj3, Subj4,
                                       Subj5, Subj6, Subj7, Subj8, Subj9) (I) =
                           NoSubject))) and
                    P.NumberOfPupils = P'Old.NumberOfPupils + 1 and
                    P.PupilEntries (P.NumberOfPupils) =
                       (Surname => SName, Forename => FName, Form => Fm,
                        -- If this is changed to a more sensible (given the
                        -- rst of the postcondition) to P'Old and removing
                        -- the 'Old from Scores the unreferenced symbol
                        -- is eliminated
                        Scores => P.PupilEntries (P.NumberOfPupils + 1).
                                  Scores'Old'Update

                          (Subj0 => (True, Score0), Subj1 => (True, Score1),
                           Subj2 => (True, Score2), Subj3 => (True, Score3),
                           Subj4 => (True, Score4), Subj5 => (True, Score5),
                           Subj6 => (True, Score6), Subj7 => (True, Score7),
                           Subj8 => (True, Score8), Subj9 => (True, Score9))))
                 else
                    P.NumberOfPupils = P'Old.NumberofPupils);

end Pupils;

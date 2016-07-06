package Dev is

    type Device (Port : not null access Integer)
    is tagged limited private;

private

    type Device (Port : not null access Integer)
    is tagged limited record
       null;
    end record;

end Dev;

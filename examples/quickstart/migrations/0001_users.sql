CREATE SCHEMA app;

CREATE DOMAIN app.email_address AS text
  CONSTRAINT email_address_shape CHECK (
    char_length(VALUE) BETWEEN 3 AND 320
    AND position('@' IN VALUE) > 1
  );

CREATE TABLE app.users (
  id bigint GENERATED ALWAYS AS IDENTITY PRIMARY KEY,
  email app.email_address NOT NULL UNIQUE,
  display_name text NOT NULL
);

CREATE SCHEMA app;

CREATE TYPE app.user_status AS ENUM (
  'pending',
  'active',
  'disabled'
);

CREATE DOMAIN app.email_address AS text
  NOT NULL
  CONSTRAINT email_address_shape CHECK (
    char_length(VALUE) BETWEEN 3 AND 320
    AND position('@' IN VALUE) > 1
  );

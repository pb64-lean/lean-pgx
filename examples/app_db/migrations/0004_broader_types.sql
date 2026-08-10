CREATE EXTENSION citext WITH SCHEMA app VERSION '1.6';

CREATE TYPE app.contact_card AS (
  label varchar(40),
  status app.user_status,
  email app.email_address
);

CREATE TYPE app.score_range AS RANGE (
  subtype = integer,
  multirange_type_name = app.score_multirange
);

CREATE FUNCTION app.audit_int4_diff(left_value integer, right_value integer)
RETURNS double precision
LANGUAGE sql
IMMUTABLE
STRICT
PARALLEL SAFE
AS $function$
  SELECT left_value::double precision - right_value::double precision
$function$;

CREATE TYPE app.audit_range AS RANGE (
  subtype = integer,
  multirange_type_name = app.audit_multirange,
  subtype_diff = app.audit_int4_diff
);

CREATE TYPE app.audit_text_range AS RANGE (
  subtype = text,
  collation = pg_catalog."C",
  subtype_opclass = pg_catalog.text_ops,
  multirange_type_name = app.audit_text_multirange
);

CREATE TABLE app.type_samples (
  id bigint GENERATED ALWAYS AS IDENTITY,
  statuses app.user_status[] NOT NULL,
  emails app.email_address[] NOT NULL,
  card app.contact_card NOT NULL,
  score app.score_range NOT NULL,
  scores app.score_multirange NOT NULL,
  amount numeric(6, 2) NOT NULL,
  observed_at time(3) NOT NULL,
  nickname app.citext NOT NULL,
  aliases app.citext[] NOT NULL,
  labels varchar(8)[] NOT NULL,
  CONSTRAINT type_samples_pkey PRIMARY KEY (id)
);

CREATE VIEW app.type_sample_summary AS
SELECT
  sample.id,
  cardinality(sample.statuses) AS status_count,
  sample.amount
FROM app.type_samples AS sample;

CREATE FUNCTION app.list_type_sample_summaries(minimum numeric(6, 2) DEFAULT 0)
RETURNS SETOF app.type_sample_summary
LANGUAGE sql
STABLE
AS $function$
  SELECT summary.id, summary.status_count, summary.amount
  FROM app.type_sample_summary AS summary
  WHERE summary.amount >= minimum
  ORDER BY summary.id
$function$;

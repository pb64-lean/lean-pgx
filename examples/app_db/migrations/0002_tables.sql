CREATE TABLE app.organizations (
  id bigint GENERATED ALWAYS AS IDENTITY,
  slug text NOT NULL,
  display_name text NOT NULL,
  created_at timestamp with time zone NOT NULL DEFAULT CURRENT_TIMESTAMP,
  CONSTRAINT organizations_pkey PRIMARY KEY (id),
  CONSTRAINT organizations_slug_key UNIQUE (slug),
  CONSTRAINT organizations_display_name_not_blank CHECK (
    char_length(btrim(display_name)) > 0
  )
);

CREATE TABLE app.users (
  id bigint GENERATED ALWAYS AS IDENTITY,
  organization_id bigint NOT NULL,
  email app.email_address NOT NULL,
  status app.user_status NOT NULL DEFAULT 'pending'::app.user_status,
  display_name text,
  created_at timestamp with time zone NOT NULL DEFAULT CURRENT_TIMESTAMP,
  CONSTRAINT users_pkey PRIMARY KEY (id),
  CONSTRAINT users_email_key UNIQUE (email),
  CONSTRAINT users_organization_email_key UNIQUE (organization_id, email),
  CONSTRAINT users_organization_fk FOREIGN KEY (organization_id)
    REFERENCES app.organizations (id),
  CONSTRAINT users_display_name_not_blank CHECK (
    display_name IS NULL OR char_length(btrim(display_name)) > 0
  )
);

CREATE TABLE app.user_profiles (
  user_id bigint NOT NULL,
  bio text NOT NULL,
  avatar_url text,
  updated_at timestamp with time zone NOT NULL DEFAULT CURRENT_TIMESTAMP,
  CONSTRAINT user_profiles_pkey PRIMARY KEY (user_id),
  CONSTRAINT user_profiles_user_fk FOREIGN KEY (user_id)
    REFERENCES app.users (id) ON DELETE CASCADE,
  CONSTRAINT user_profiles_bio_length CHECK (char_length(bio) <= 500)
);

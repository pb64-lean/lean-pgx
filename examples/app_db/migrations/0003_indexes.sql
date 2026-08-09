CREATE INDEX users_organization_status_idx
  ON app.users (organization_id, status);

CREATE INDEX users_active_created_at_idx
  ON app.users (created_at)
  WHERE status = 'active'::app.user_status;
